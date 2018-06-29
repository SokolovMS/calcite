/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to you under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.calcite.rel.rules;

import org.apache.calcite.plan.RelOptCluster;
import org.apache.calcite.plan.RelOptRule;
import org.apache.calcite.plan.RelOptRuleCall;
import org.apache.calcite.plan.RelOptRuleOperand;
import org.apache.calcite.rel.RelNode;
import org.apache.calcite.rel.core.Aggregate;
import org.apache.calcite.rel.core.AggregateCall;
import org.apache.calcite.rel.core.RelFactories;
import org.apache.calcite.rel.logical.LogicalAggregate;
import org.apache.calcite.rel.type.RelDataType;
import org.apache.calcite.rel.type.RelDataTypeFactory;
import org.apache.calcite.rel.type.RelDataTypeField;
import org.apache.calcite.rex.RexBuilder;
import org.apache.calcite.rex.RexLiteral;
import org.apache.calcite.rex.RexNode;
import org.apache.calcite.sql.SqlAggFunction;
import org.apache.calcite.sql.SqlKind;
import org.apache.calcite.sql.fun.SqlStdOperatorTable;
import org.apache.calcite.sql.type.SqlTypeUtil;
import org.apache.calcite.tools.RelBuilder;
import org.apache.calcite.tools.RelBuilderFactory;
import org.apache.calcite.util.CompositeList;
import org.apache.calcite.util.ImmutableIntList;
import org.apache.calcite.util.Util;

import com.google.common.collect.ImmutableList;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Planner rule that reduces aggregate functions in
 * {@link org.apache.calcite.rel.core.Aggregate}s to simpler forms.
 *
 * <p>Rewrites:
 * <ul>
 *
 * <li>AVG(x) &rarr; SUM(x) / COUNT(x)
 *
 * <li>STDDEV_POP(x) &rarr; SQRT(
 *     (SUM(x * x) - SUM(x) * SUM(x) / COUNT(x))
 *    / COUNT(x))
 *
 * <li>STDDEV_SAMP(x) &rarr; SQRT(
 *     (SUM(x * x) - SUM(x) * SUM(x) / COUNT(x))
 *     / CASE COUNT(x) WHEN 1 THEN NULL ELSE COUNT(x) - 1 END)
 *
 * <li>VAR_POP(x) &rarr; (SUM(x * x) - SUM(x) * SUM(x) / COUNT(x))
 *     / COUNT(x)
 *
 * <li>VAR_SAMP(x) &rarr; (SUM(x * x) - SUM(x) * SUM(x) / COUNT(x))
 *        / CASE COUNT(x) WHEN 1 THEN NULL ELSE COUNT(x) - 1 END
 *
 * <li>CORR(x, y) &rarr; COVAR_POP(x, y) / (STDDEV_POP(x) * STDDEV_POP(y))
 *
 * <li>COVAR_POP(x, y) &rarr; (SUM(x * y) - SUM(x, y) * SUM(y, x)
 *     / REGR_COUNT(x, y)) / REGR_COUNT(x, y)
 *
 * <li>COVAR_SAMP(x, y) &rarr; (SUM(x * y) - SUM(x, y) * SUM(y, x) / REGR_COUNT(x, y))
 *     / CASE REGR_COUNT(x, y) WHEN 1 THEN NULL ELSE REGR_COUNT(x, y) - 1 END
 *
 * <li>REGR_AVGX(x, y) &rarr; SUM(y, x) / REGR_COUNT(x, y)
 *
 * <li>REGR_AVGY(x, y) &rarr; SUM(x, y) / REGR_COUNT(x, y)
 *
 * <li>REGR_INTERCEPT(x, y) &rarr; REGR_AVGY(x, y) - REGR_SLOPE(x, y) * REGR_AVGX(x, y)
 *
 * <li>REGR_R2(x, y) &rarr; CASE WHEN VAR_POP(y) = 0 THEN NULL
 *     WHEN VAR_POP(x) WHEN 0 THEN 1 ELSE
 *
 * <li>REGR_SLOPE(x, y) &rarr; COVAR_POP(x, y) / VAR_POP(y)
 *
 * <li>REGR_SXX(x, y) &rarr; REGR_COUNT(x, y) * VAR_POP(y)
 *
 * <li>REGR_SXY(x, y) &rarr; REGR_COUNT(x, y) * COVAR_POP(x, y)
 *
 * <li>REGR_SYY(x, y) &rarr; REGR_COUNT(x, y) * VAR_POP(x)
 *
 * </ul>
 *
 * <p>Since many of these rewrites introduce multiple occurrences of simpler
 * forms like {@code COUNT(x)}, the rule gathers common sub-expressions as it
 * goes.
 */
public class AggregateReduceFunctionsRule extends RelOptRule {
  //~ Static fields/initializers ---------------------------------------------

  /** The singleton. */
  public static final AggregateReduceFunctionsRule INSTANCE =
      new AggregateReduceFunctionsRule(operand(LogicalAggregate.class, any()),
          RelFactories.LOGICAL_BUILDER);

  //~ Constructors -----------------------------------------------------------

  /** Creates an AggregateReduceFunctionsRule. */
  public AggregateReduceFunctionsRule(RelOptRuleOperand operand,
      RelBuilderFactory relBuilderFactory) {
    super(operand, relBuilderFactory, null);
  }

  //~ Methods ----------------------------------------------------------------

  @Override public boolean matches(RelOptRuleCall call) {
    if (!super.matches(call)) {
      return false;
    }
    Aggregate oldAggRel = (Aggregate) call.rels[0];
    return containsAvgStddevVarCall(oldAggRel.getAggCallList());
  }

  public void onMatch(RelOptRuleCall ruleCall) {
    Aggregate oldAggRel = (Aggregate) ruleCall.rels[0];
    reduceAggs(ruleCall, oldAggRel);
  }

  /**
   * Returns whether any of the aggregates are calls to AVG, STDDEV_*, VAR_*.
   *
   * @param aggCallList List of aggregate calls
   */
  private boolean containsAvgStddevVarCall(List<AggregateCall> aggCallList) {
    for (AggregateCall call : aggCallList) {
      if (isReducible(call.getAggregation().getKind())) {
        return true;
      }
    }
    return false;
  }

  /**
   * Returns whether the aggregate call is a reducible function
   */
  private boolean isReducible(final SqlKind kind) {
    if (SqlKind.AVG_AGG_FUNCTIONS.contains(kind)
        || SqlKind.COVAR_AVG_AGG_FUNCTIONS.contains(kind)) {
      return true;
    }
    switch (kind) {
    case SUM:
      return true;
    }
    return false;
  }

  /**
   * Reduces all calls to AVG, STDDEV_POP, STDDEV_SAMP, VAR_POP, VAR_SAMP in
   * the aggregates list to.
   *
   * <p>It handles newly generated common subexpressions since this was done
   * at the sql2rel stage.
   */
  private void reduceAggs(
      RelOptRuleCall ruleCall,
      Aggregate oldAggRel) {
    RexBuilder rexBuilder = oldAggRel.getCluster().getRexBuilder();

    List<AggregateCall> oldCalls = oldAggRel.getAggCallList();
    final int groupCount = oldAggRel.getGroupCount();
    final int indicatorCount = oldAggRel.getIndicatorCount();

    final List<AggregateCall> newCalls = new ArrayList<>();
    final Map<AggregateCall, RexNode> aggCallMapping = new HashMap<>();

    final List<RexNode> projList = new ArrayList<>();

    // pass through group key (+ indicators if present)
    for (int i = 0; i < groupCount + indicatorCount; ++i) {
      projList.add(
          rexBuilder.makeInputRef(
              getFieldType(oldAggRel, i),
              i));
    }

    // List of input expressions. If a particular aggregate needs more, it
    // will add an expression to the end, and we will create an extra
    // project.
    final RelBuilder relBuilder = ruleCall.builder();
    relBuilder.push(oldAggRel.getInput());
    final List<RexNode> inputExprs = new ArrayList<>(relBuilder.fields());

    // create new agg function calls and rest of project list together
    for (AggregateCall oldCall : oldCalls) {
      projList.add(
          reduceAgg(
              oldAggRel, oldCall, newCalls, aggCallMapping, inputExprs));
    }

    final int extraArgCount =
        inputExprs.size() - relBuilder.peek().getRowType().getFieldCount();
    if (extraArgCount > 0) {
      relBuilder.project(inputExprs,
          CompositeList.of(
              relBuilder.peek().getRowType().getFieldNames(),
              Collections.nCopies(extraArgCount, null)));
    }
    newAggregateRel(relBuilder, oldAggRel, newCalls);
    newCalcRel(relBuilder, oldAggRel.getRowType(), projList);
    RelNode build = relBuilder.build();
    ruleCall.transformTo(build);
  }

  private RexNode reduceAgg(
      Aggregate oldAggRel,
      AggregateCall oldCall,
      List<AggregateCall> newCalls,
      Map<AggregateCall, RexNode> aggCallMapping,
      List<RexNode> inputExprs) {
    final SqlKind kind = oldCall.getAggregation().getKind();
    if (isReducible(kind)) {
      switch (kind) {
      case SUM:
        // replace original SUM(x) with
        // case COUNT(x) when 0 then null else SUM0(x) end
        return reduceSum(oldAggRel, oldCall, newCalls, aggCallMapping);
      case AVG:
        // replace original AVG(x) with SUM(x) / COUNT(x)
        return reduceAvg(oldAggRel, oldCall, newCalls, aggCallMapping, inputExprs);
      case CORR:
        // replace original CORR(x, y) with
        //   COVAR_POP(x,  y) / (STDDEV_POP(x) * STDDEV_POP(y))
        return reduceCorr(oldAggRel, oldCall, newCalls, aggCallMapping, inputExprs);
      case COVAR_POP:
        // replace original COVAR_POP(x, y) with
        //     (SUM(x * y) - SUM(y) * SUM(y) / COUNT(x))
        //     / COUNT(x))
        return reduceCovariance(oldAggRel, oldCall, true, false, newCalls,
            aggCallMapping, inputExprs);
      case COVAR_SAMP:
        // replace original COVAR_SAMP(x, y) with
        //   SQRT(
        //     (SUM(x * y) - SUM(x) * SUM(y) / COUNT(x))
        //     / CASE COUNT(x) WHEN 1 THEN NULL ELSE COUNT(x) - 1 END)
        return reduceCovariance(oldAggRel, oldCall, false, false, newCalls,
            aggCallMapping, inputExprs);
      case REGR_AVGX:
        // replace original REGR_AVGX(x, y) with
        // SUM(x, y) / REGR_COUNT(x, y)
        return reduceAvgZ(oldAggRel, oldCall, newCalls, aggCallMapping, true);
      case REGR_AVGY:
        // replace original REGR_AVGY(x, y) with
        // SUM(y, x) / REGR_COUNT(x, y)
        return reduceAvgZ(oldAggRel, oldCall, newCalls, aggCallMapping, false);
      case REGR_SXX:
        // replace original REGR_SXX(x, y) with
        // REGR_COUNT(x, y) * VAR_POP(y)
        return reduceRegrSzz(oldAggRel, oldCall, newCalls, aggCallMapping, inputExprs, false, true);
      case REGR_SXY:
        // replace original REGR_SXY(x, y) with
        // REGR_COUNT(x, y) * COVAR_POP(x, y)
        return reduceRegrSzz(oldAggRel, oldCall, newCalls, aggCallMapping, inputExprs, true, true);
      case REGR_SYY:
        // replace original REGR_SYY(x, y) with
        // REGR_COUNT(x, y) * VAR_POP(x)
        return reduceRegrSzz(oldAggRel, oldCall, newCalls,
            aggCallMapping, inputExprs, false, false);
      case STDDEV_POP:
        // replace original STDDEV_POP(x) with
        //   SQRT(
        //     (SUM(x * x) - SUM(x) * SUM(x) / COUNT(x))
        //     / COUNT(x))
        return reduceStddev(oldAggRel, oldCall, true, true, newCalls,
            aggCallMapping, inputExprs);
      case STDDEV_SAMP:
        // replace original STDDEV_POP(x) with
        //   SQRT(
        //     (SUM(x * x) - SUM(x) * SUM(x) / COUNT(x))
        //     / CASE COUNT(x) WHEN 1 THEN NULL ELSE COUNT(x) - 1 END)
        return reduceStddev(oldAggRel, oldCall, false, true, newCalls,
            aggCallMapping, inputExprs);
      case VAR_POP:
        // replace original VAR_POP(x) with
        //     (SUM(x * x) - SUM(x) * SUM(x) / COUNT(x))
        //     / COUNT(x)
        return reduceStddev(oldAggRel, oldCall, true, false, newCalls,
            aggCallMapping, inputExprs);
      case REGR_INTERCEPT:
        // replace original REGR_INTERCEPT(x, y) with
        //     REGR_AVGX(x, y) - REGR_SLOPE(x, y) * REGR_AVGY(x, y)
        return reduceRegrIntercept(oldAggRel, oldCall, newCalls, aggCallMapping, inputExprs);
      case REGR_R2:
        return reduceRegrR2(oldAggRel, oldCall, newCalls, aggCallMapping, inputExprs);
      case REGR_SLOPE:
        // replace original REGR_SLOPE(X, Y) with
        //     COVAR_POP(x * y) / VAR_POP(y)
        return reduceRegrSlope(oldAggRel, oldCall, newCalls, aggCallMapping, inputExprs);
      case VAR_SAMP:
        // replace original VAR_POP(x) with
        //     (SUM(x * x) - SUM(x) * SUM(x) / COUNT(x))
        //     / CASE COUNT(x) WHEN 1 THEN NULL ELSE COUNT(x) - 1 END
        return reduceStddev(oldAggRel, oldCall, false, false, newCalls,
            aggCallMapping, inputExprs);
      default:
        throw Util.unexpected(kind);
      }
    } else {
      // anything else:  preserve original call
      RexBuilder rexBuilder = oldAggRel.getCluster().getRexBuilder();
      final int nGroups = oldAggRel.getGroupCount();
      List<RelDataType> oldArgTypes =
          SqlTypeUtil.projectTypes(
              oldAggRel.getInput().getRowType(), oldCall.getArgList());
      return rexBuilder.addAggCall(oldCall,
          nGroups,
          oldAggRel.indicator,
          newCalls,
          aggCallMapping,
          oldArgTypes);
    }
  }

  private AggregateCall createAggregateCallWithBinding(
      RelDataTypeFactory typeFactory,
      SqlAggFunction aggFunction,
      RelDataType operandType,
      Aggregate oldAggRel,
      AggregateCall oldCall,
      List<Integer> argOrdinals) {
    final Aggregate.AggCallBinding binding =
        new Aggregate.AggCallBinding(typeFactory, aggFunction,
            ImmutableList.of(operandType), oldAggRel.getGroupCount(),
            oldCall.filterArg >= 0);
    return AggregateCall.create(aggFunction,
        oldCall.isDistinct(),
        oldCall.isApproximate(),
        argOrdinals,
        oldCall.filterArg,
        aggFunction.inferReturnType(binding),
        null);
  }

  private RexNode reduceAvg(
      Aggregate oldAggRel,
      AggregateCall oldCall,
      List<AggregateCall> newCalls,
      Map<AggregateCall, RexNode> aggCallMapping,
      List<RexNode> inputExprs) {
    final int nGroups = oldAggRel.getGroupCount();
    final RexBuilder rexBuilder = oldAggRel.getCluster().getRexBuilder();
    final int iAvgInput = oldCall.getArgList().get(0);
    final RelDataType avgInputType =
        getFieldType(
            oldAggRel.getInput(),
            iAvgInput);
    final AggregateCall sumCall =
        AggregateCall.create(SqlStdOperatorTable.SUM,
            oldCall.isDistinct(),
            oldCall.isApproximate(),
            oldCall.getArgList(),
            oldCall.filterArg,
            oldAggRel.getGroupCount(),
            oldAggRel.getInput(),
            null,
            null);
    final AggregateCall countCall =
        AggregateCall.create(SqlStdOperatorTable.COUNT,
            oldCall.isDistinct(),
            oldCall.isApproximate(),
            oldCall.getArgList(),
            oldCall.filterArg,
            oldAggRel.getGroupCount(),
            oldAggRel.getInput(),
            null,
            null);

    // NOTE:  these references are with respect to the output
    // of newAggRel
    RexNode numeratorRef =
        rexBuilder.addAggCall(sumCall,
            nGroups,
            oldAggRel.indicator,
            newCalls,
            aggCallMapping,
            ImmutableList.of(avgInputType));
    final RexNode denominatorRef =
        rexBuilder.addAggCall(countCall,
            nGroups,
            oldAggRel.indicator,
            newCalls,
            aggCallMapping,
            ImmutableList.of(avgInputType));

    final RelDataTypeFactory typeFactory = oldAggRel.getCluster().getTypeFactory();
    final RelDataType avgType = typeFactory.createTypeWithNullability(
        oldCall.getType(), numeratorRef.getType().isNullable());
    numeratorRef = rexBuilder.ensureType(avgType, numeratorRef, true);
    final RexNode divideRef =
        rexBuilder.makeCall(SqlStdOperatorTable.DIVIDE, numeratorRef, denominatorRef);
    return rexBuilder.makeCast(oldCall.getType(), divideRef);
  }

  private RexNode reduceSum(
      Aggregate oldAggRel,
      AggregateCall oldCall,
      List<AggregateCall> newCalls,
      Map<AggregateCall, RexNode> aggCallMapping) {
    final int nGroups = oldAggRel.getGroupCount();
    RexBuilder rexBuilder = oldAggRel.getCluster().getRexBuilder();
    int size = oldCall.getArgList().size();
    int arg = oldCall.getArgList().get(0);
    RelDataType argType =
        getFieldType(
            oldAggRel.getInput(),
            arg);
    RelDataType argType2 = null;
    int arg2 = 0;
    SqlAggFunction countFunction = SqlStdOperatorTable.COUNT;
    List<RelDataType> aggArgTypes = ImmutableList.of(argType);
    if (size == 2) {
      arg2 = oldCall.getArgList().get(1);
      argType2 = getFieldType(oldAggRel.getInput(), arg2);
      countFunction = SqlStdOperatorTable.REGR_COUNT;
      aggArgTypes = ImmutableList.of(argType, argType2);
    }

    final AggregateCall sumZeroCall =
        AggregateCall.create(SqlStdOperatorTable.SUM0, oldCall.isDistinct(),
            oldCall.isApproximate(), oldCall.getArgList(), oldCall.filterArg,
            oldAggRel.getGroupCount(), oldAggRel.getInput(), null,
            oldCall.name);
    final AggregateCall countCall =
        AggregateCall.create(countFunction,
            oldCall.isDistinct(),
            oldCall.isApproximate(),
            oldCall.getArgList(),
            oldCall.filterArg,
            oldAggRel.getGroupCount(),
            oldAggRel,
            null,
            null);

    // NOTE:  these references are with respect to the output
    // of newAggRel
    RexNode sumZeroRef =
        rexBuilder.addAggCall(sumZeroCall,
            nGroups,
            oldAggRel.indicator,
            newCalls,
            aggCallMapping,
            aggArgTypes);
    if (!oldCall.getType().isNullable()) {
      // If SUM(x) is not nullable, the validator must have determined that
      // nulls are impossible (because the group is never empty and x is never
      // null). Therefore we translate to SUM0(x).
      return sumZeroRef;
    }
    RexNode countRef =
        rexBuilder.addAggCall(countCall,
            nGroups,
            oldAggRel.indicator,
            newCalls,
            aggCallMapping,
            aggArgTypes);
    return rexBuilder.makeCall(SqlStdOperatorTable.CASE,
        rexBuilder.makeCall(SqlStdOperatorTable.EQUALS,
            countRef, rexBuilder.makeExactLiteral(BigDecimal.ZERO)),
        rexBuilder.makeCast(sumZeroRef.getType(), rexBuilder.constantNull()),
        sumZeroRef);
  }

  private RexNode reduceRegrIntercept(
          Aggregate oldAggRel,
          AggregateCall oldCall,
          List<AggregateCall> newCalls,
          Map<AggregateCall, RexNode> aggCallMapping,
          List<RexNode> inputExprs) {
    // regr_intercept(x, y) ==>
    //     regr_avgx(x, y) - regr_slope(x, y) * regr_avgy(x, y)

    final RelOptCluster cluster = oldAggRel.getCluster();
    final RexBuilder rexBuilder = cluster.getRexBuilder();

    assert oldCall.getArgList().size() == 2 : oldCall.getArgList();
    final RexNode avgX = reduceAvgZ(oldAggRel, oldCall,  newCalls,
            aggCallMapping, true);
    final RexNode avgY = reduceAvgZ(oldAggRel, oldCall,  newCalls,
            aggCallMapping, false);
    final RexNode regrSlope = reduceRegrSlope(oldAggRel, oldCall, newCalls,
            aggCallMapping, inputExprs);
    final RexNode product = rexBuilder.makeCall(SqlStdOperatorTable.MULTIPLY, regrSlope, avgY);
    final RexNode result = rexBuilder.makeCall(SqlStdOperatorTable.MINUS, avgX, product);
    return rexBuilder.makeCast(oldCall.getType(), result);
  }

  private RexNode reduceRegrR2(
          Aggregate oldAggRel,
          AggregateCall oldCall,
          List<AggregateCall> newCalls,
          Map<AggregateCall, RexNode> aggCallMapping,
          List<RexNode> inputExprs) {
    // regr_r2(x, y) ==>
    //     covar_pop(x * y) / var_pop(y)
    assert oldCall.getArgList().size() == 2 : oldCall.getArgList();
    final RelOptCluster cluster = oldAggRel.getCluster();
    final RexBuilder rexBuilder = cluster.getRexBuilder();

    final int argXOrdinal = oldCall.getArgList().get(0);
    final int argYOrdinal = oldCall.getArgList().get(1);
    final RelDataType argXOrdinalType = getFieldType(oldAggRel.getInput(), argXOrdinal);
    final RelDataType argYOrdinalType = getFieldType(oldAggRel.getInput(), argYOrdinal);
    final RelDataType oldCallType =
        cluster.getTypeFactory().createTypeWithNullability(oldCall.getType(),
            argXOrdinalType.isNullable() || argYOrdinalType.isNullable());
    final RexNode argX = rexBuilder.ensureType(oldCallType, inputExprs.get(argXOrdinal), true);
    final RexNode argY = rexBuilder.ensureType(oldCallType, inputExprs.get(argYOrdinal), true);
    final RexNode varPopX = getCovarianceNode(oldAggRel, oldCall, true, false, newCalls,
        aggCallMapping, oldCallType, argX, argX, inputExprs);
    final RexNode varPopY = getCovarianceNode(oldAggRel, oldCall, true, false, newCalls,
        aggCallMapping, oldCallType, argY, argY, inputExprs);
    final RexNode corr = reduceCorr(oldAggRel, oldCall, newCalls, aggCallMapping, inputExprs);
    RexLiteral zero = rexBuilder.makeExactLiteral(BigDecimal.ZERO);
    RexNode[] whenThenElse = {
        // when x is null
        rexBuilder.makeCall(SqlStdOperatorTable.EQUALS, varPopY, zero),
        // then return y is [not] null
        rexBuilder.constantNull(),

        // when y is null
        rexBuilder.makeCall(SqlStdOperatorTable.AND,
            rexBuilder.makeCall(SqlStdOperatorTable.EQUALS, varPopX, zero),
            rexBuilder.makeCall(SqlStdOperatorTable.NOT_EQUALS, varPopY, zero)),

        // then return x is [not] null
        rexBuilder.makeExactLiteral(BigDecimal.ONE),

        rexBuilder.makeCall(SqlStdOperatorTable.AND,
            rexBuilder.makeCall(SqlStdOperatorTable.GREATER_THAN, varPopX, zero),
            rexBuilder.makeCall(SqlStdOperatorTable.NOT_EQUALS, varPopY, zero)),

        rexBuilder.makeCall(SqlStdOperatorTable.MULTIPLY, corr, corr),
        // else return x compared to y
        rexBuilder.constantNull()
    };
    final RexNode result = rexBuilder.makeCall(SqlStdOperatorTable.CASE, whenThenElse);
    return rexBuilder.makeCast(oldCall.getType(), result);
  }

  private RexNode reduceRegrSlope(
      Aggregate oldAggRel,
      AggregateCall oldCall,
      List<AggregateCall> newCalls,
      Map<AggregateCall, RexNode> aggCallMapping,
      List<RexNode> inputExprs) {
    // regr_slope(x, y) ==>
    //     covar_pop(x * y) / var_pop(y)

    final RelOptCluster cluster = oldAggRel.getCluster();
    final RexBuilder rexBuilder = cluster.getRexBuilder();
    final RelDataTypeFactory typeFactory = cluster.getTypeFactory();

    assert oldCall.getArgList().size() == 2 : oldCall.getArgList();
    final int argXOrdinal = oldCall.getArgList().get(0);
    final int argYOrdinal = oldCall.getArgList().get(1);
    int arg = oldCall.getArgList().get(0);
    RelDataType argXType = getFieldType(oldAggRel.getInput(), arg);
    RelDataType argYType = getFieldType(oldAggRel.getInput(), arg);
    final RelDataType argXOrdinalType = getFieldType(oldAggRel.getInput(), argXOrdinal);
    final RelDataType argYOrdinalType = getFieldType(oldAggRel.getInput(), argYOrdinal);
    final RelDataType oldCallType =
            cluster.getTypeFactory().createTypeWithNullability(oldCall.getType(),
                    argXOrdinalType.isNullable() || argYOrdinalType.isNullable());
    final RexNode argX = rexBuilder.ensureType(argXType, inputExprs.get(argXOrdinal), true);
    final RexNode argY = rexBuilder.ensureType(argYType, inputExprs.get(argYOrdinal), true);
    final RexNode covarPop = getCovarianceNode(oldAggRel, oldCall, true, false, newCalls,
            aggCallMapping, oldCallType, argX, argY, inputExprs);
    final RexNode varPop = getCovarianceNode(oldAggRel, oldCall, true, false, newCalls,
            aggCallMapping, oldCallType, argY, argY, inputExprs);
    final RexNode result = rexBuilder.makeCall(SqlStdOperatorTable.DIVIDE, covarPop, varPop);
    return rexBuilder.makeCast(oldCall.getType(), result);
  }

  private RexNode reduceStddev(
      Aggregate oldAggRel,
      AggregateCall oldCall,
      boolean biased,
      boolean sqrt,
      List<AggregateCall> newCalls,
      Map<AggregateCall, RexNode> aggCallMapping,
      List<RexNode> inputExprs) {
    // stddev_pop(x) ==>
    //   power(
    //     (sum(x * x) - sum(x) * sum(x) / count(x))
    //     / count(x),
    //     .5)
    //
    // stddev_samp(x) ==>
    //   power(
    //     (sum(x * x) - sum(x) * sum(x) / count(x))
    //     / nullif(count(x) - 1, 0),
    //     .5)
    final RelOptCluster cluster = oldAggRel.getCluster();
    final RexBuilder rexBuilder = cluster.getRexBuilder();
    final RelDataTypeFactory typeFactory = cluster.getTypeFactory();

    assert oldCall.getArgList().size() == 1 : oldCall.getArgList();
    final int argOrdinal = oldCall.getArgList().get(0);
    final RelDataType argOrdinalType = getFieldType(oldAggRel.getInput(), argOrdinal);
    final RelDataType oldCallType =
        typeFactory.createTypeWithNullability(oldCall.getType(),
            argOrdinalType.isNullable());

    final RexNode argRef =
        rexBuilder.ensureType(oldCallType, inputExprs.get(argOrdinal), true);
    return getCovarianceNode(oldAggRel, oldCall, biased, sqrt,
        newCalls, aggCallMapping, oldCallType, argRef, argRef, inputExprs);
  }

  private RexNode getCovarianceNode(Aggregate oldAggRel,
      AggregateCall oldCall,
      boolean biased,
      boolean sqrt,
      List<AggregateCall> newCalls,
      Map<AggregateCall, RexNode> aggCallMapping,
      RelDataType oldCallType,
      RexNode argRef1,
      RexNode argRef2,
      List<RexNode> inputExprs) {
    final RelOptCluster cluster = oldAggRel.getCluster();
    final RexBuilder rexBuilder = cluster.getRexBuilder();
    final int argOrdinal = oldCall.getArgList().get(0);
    final RelDataType argOrdinalType = getFieldType(oldAggRel.getInput(), argOrdinal);
    final RexNode argSquared = rexBuilder.makeCall(SqlStdOperatorTable.MULTIPLY, argRef1, argRef2);
    final int argSquaredOrdinal = lookupOrAdd(inputExprs, argSquared);
    final RelDataTypeFactory typeFactory = cluster.getTypeFactory();
    final AggregateCall sumArgSquaredAggCall =
        createAggregateCallWithBinding(typeFactory, SqlStdOperatorTable.SUM,
            argSquared.getType(), oldAggRel, oldCall, ImmutableList.of(argSquaredOrdinal));

    final int nGroups = oldAggRel.getGroupCount();
    final RexNode sumArgSquared =
        rexBuilder.addAggCall(sumArgSquaredAggCall,
            nGroups,
            oldAggRel.indicator,
            newCalls,
            aggCallMapping,
            ImmutableList.of(sumArgSquaredAggCall.getType()));

    final AggregateCall sumArgAggCall =
        AggregateCall.create(SqlStdOperatorTable.SUM,
            oldCall.isDistinct(),
            oldCall.isApproximate(),
            ImmutableIntList.of(argOrdinal),
            oldCall.filterArg,
            oldAggRel.getGroupCount(),
            oldAggRel.getInput(),
            null,
            null);

    final RexNode sumArg =
        rexBuilder.addAggCall(sumArgAggCall,
            nGroups,
            oldAggRel.indicator,
            newCalls,
            aggCallMapping,
            ImmutableList.of(sumArgAggCall.getType()));
    final RexNode sumArgCast = rexBuilder.ensureType(oldCallType, sumArg, true);
    final RexNode sumSquaredArg =
        rexBuilder.makeCall(
            SqlStdOperatorTable.MULTIPLY, sumArgCast, sumArgCast);

    final AggregateCall countArgAggCall =
        AggregateCall.create(argRef1 == argRef2
               ? SqlStdOperatorTable.COUNT
               : SqlStdOperatorTable.REGR_COUNT,
            oldCall.isDistinct(),
            oldCall.isApproximate(),
            oldCall.getArgList(),
            oldCall.filterArg,
            oldAggRel.getGroupCount(),
            oldAggRel,
            null,
            null);

    final RexNode countArg =
        rexBuilder.addAggCall(countArgAggCall,
            nGroups,
            oldAggRel.indicator,
            newCalls,
            aggCallMapping,
            ImmutableList.of(argOrdinalType));

    final RexNode avgSumSquaredArg =
        rexBuilder.makeCall(
            SqlStdOperatorTable.DIVIDE, sumSquaredArg, countArg);

    final RexNode diff =
        rexBuilder.makeCall(
            SqlStdOperatorTable.MINUS,
            sumArgSquared, avgSumSquaredArg);

    final RexNode denominator;
    if (biased) {
      denominator = countArg;
    } else {
      final RexLiteral one =
          rexBuilder.makeExactLiteral(BigDecimal.ONE);
      final RexNode nul =
          rexBuilder.makeCast(countArg.getType(), rexBuilder.constantNull());
      final RexNode countMinusOne =
          rexBuilder.makeCall(
              SqlStdOperatorTable.MINUS, countArg, one);
      final RexNode countEqOne =
          rexBuilder.makeCall(
              SqlStdOperatorTable.EQUALS, countArg, one);
      denominator =
          rexBuilder.makeCall(
              SqlStdOperatorTable.CASE,
              countEqOne, nul, countMinusOne);
    }

    final RexNode div =
        rexBuilder.makeCall(
            SqlStdOperatorTable.DIVIDE, diff, denominator);

    RexNode result = div;
    if (sqrt) {
      final RexNode half =
          rexBuilder.makeExactLiteral(new BigDecimal("0.5"));
      result =
          rexBuilder.makeCall(
              SqlStdOperatorTable.POWER, div, half);
    }

    return rexBuilder.makeCast(
        oldCall.getType(), result);
  }

  private RexNode reduceRegrSzz(
      Aggregate oldAggRel,
      AggregateCall oldCall,
      List<AggregateCall> newCalls,
      Map<AggregateCall, RexNode> aggCallMapping,
      List<RexNode> inputExprs,
      boolean covar,
      boolean left) {
    // regr_sxx(x, y) ==>
    //    regr_count(x * y) * var_pop(y)
    //
    // regr_sxy(x, y) ==>
    //    regr_count(x * y) * covar_pop(x, y)
    //
    // regr_syy(x, y) ==>
    //    regr_count(x * y) * var_pop(y)

    assert oldCall.getArgList().size() == 2 : oldCall.getArgList();
    final RelOptCluster cluster = oldAggRel.getCluster();
    final RexBuilder rexBuilder = cluster.getRexBuilder();
    final RelDataTypeFactory typeFactory = cluster.getTypeFactory();
    final int argOrdinal0 = oldCall.getArgList().get(0);
    final int argOrdinal1 = oldCall.getArgList().get(1);
    final RelDataType argOrdinalType0 = getFieldType(oldAggRel.getInput(), argOrdinal0);
    final RelDataType argOrdinalType1 = getFieldType(oldAggRel.getInput(), argOrdinal1);

    final int nGroups = oldAggRel.getGroupCount();

    final RelDataType oldCallType =
        typeFactory.createTypeWithNullability(oldCall.getType(),
            argOrdinalType0.isNullable() || argOrdinalType1.isNullable());

    final RexNode arg0Ref =
        rexBuilder.ensureType(oldCallType, inputExprs.get(argOrdinal0), true);
    final RexNode arg1Ref =
        rexBuilder.ensureType(oldCallType, inputExprs.get(argOrdinal1), true);

    final AggregateCall countArgAggCall =
        AggregateCall.create(SqlStdOperatorTable.REGR_COUNT,
            oldCall.isDistinct(),
            oldCall.isApproximate(),
            oldCall.getArgList(),
            oldCall.filterArg,
            oldAggRel.getGroupCount(),
            oldAggRel,
            null,
            null);

    final RexNode countArg =
        rexBuilder.addAggCall(countArgAggCall,
            nGroups,
            oldAggRel.indicator,
            newCalls,
            aggCallMapping,
            ImmutableList.of(argOrdinalType0, argOrdinalType1));

    final RexNode varCovarFactor;
    if (covar) {
      varCovarFactor = getCovarianceNode(oldAggRel, oldCall, true, false, newCalls, aggCallMapping,
          oldCallType, arg0Ref, arg1Ref, inputExprs);
    } else {
      RexNode arg = left ? arg0Ref : arg1Ref;
      varCovarFactor =
          getCovarianceNode(oldAggRel, oldCall, true, false, newCalls, aggCallMapping,
              oldCallType, arg, arg, inputExprs);
    }
    final RexNode result =
        rexBuilder.makeCall(SqlStdOperatorTable.MULTIPLY, countArg, varCovarFactor);
    return rexBuilder.makeCast(oldCall.getType(), result);
  }

  private RexNode reduceAvgZ(
      Aggregate oldAggRel,
      AggregateCall oldCall,
      List<AggregateCall> newCalls,
      Map<AggregateCall, RexNode> aggCallMapping,
      boolean avgx) {
    // regr_avgx(x, y) ==>
    //     sum(y, x) / regr_count(x, y)
    //
    // regr_avgy(x, y) ==>
    //     sum(x, y) / regr_count(x, y)

    assert oldCall.getArgList().size() == 2 : oldCall.getArgList();
    final RelOptCluster cluster = oldAggRel.getCluster();
    final RexBuilder rexBuilder = cluster.getRexBuilder();
    final RelDataTypeFactory typeFactory = cluster.getTypeFactory();
    final int argOrdinal0 = oldCall.getArgList().get(0);
    final int argOrdinal1 = oldCall.getArgList().get(1);
    final RelDataType argOrdinalType0 = getFieldType(oldAggRel.getInput(), argOrdinal0);
    final RelDataType argOrdinalType1 = getFieldType(oldAggRel.getInput(), argOrdinal1);

    final List<Integer> argOrdinals = avgx
        ? ImmutableIntList.of(argOrdinal0, argOrdinal1)
        : ImmutableIntList.of(argOrdinal1, argOrdinal0);

    final AggregateCall sumArgAggCall =
        AggregateCall.create(SqlStdOperatorTable.SUM,
            oldCall.isDistinct(),
            oldCall.isApproximate(),
            argOrdinals,
            oldCall.filterArg,
            oldAggRel.getGroupCount(),
            oldAggRel.getInput(),
            null,
            null);
    final int nGroups = oldAggRel.getGroupCount();
    final RexNode sumArg =
        rexBuilder.addAggCall(sumArgAggCall,
            nGroups,
            oldAggRel.indicator,
            newCalls,
            aggCallMapping,
            ImmutableList.of(sumArgAggCall.getType()));
    final AggregateCall countArgAggCall =
        AggregateCall.create(SqlStdOperatorTable.REGR_COUNT,
            oldCall.isDistinct(),
            oldCall.isApproximate(),
            oldCall.getArgList(),
            oldCall.filterArg,
            oldAggRel.getGroupCount(),
            oldAggRel,
            null,
            null);

    final RexNode countArg =
        rexBuilder.addAggCall(countArgAggCall,
            nGroups,
            oldAggRel.indicator,
            newCalls,
            aggCallMapping,
            ImmutableList.of(argOrdinalType0, argOrdinalType1));
    final RexNode result =
        rexBuilder.makeCall(SqlStdOperatorTable.DIVIDE, sumArg, countArg);
    return rexBuilder.makeCast(oldCall.getType(), result);
  }

  private RexNode reduceCorr(
      Aggregate oldAggRel,
      AggregateCall oldCall,
      List<AggregateCall> newCalls,
      Map<AggregateCall, RexNode> aggCallMapping,
      List<RexNode> inputExprs) {
    // corr(x, y) ==>
    //   var_pop(x) / (stddev_pop(x) * stddev_pop(y))

    assert oldCall.getArgList().size() == 2 : oldCall.getArgList();
    final RelOptCluster cluster = oldAggRel.getCluster();
    final RexBuilder rexBuilder = cluster.getRexBuilder();
    final RelDataTypeFactory typeFactory = cluster.getTypeFactory();
    final int argOrdinal0 = oldCall.getArgList().get(0);
    final int argOrdinal1 = oldCall.getArgList().get(1);
    final RelDataType argOrdinalType0 = getFieldType(oldAggRel.getInput(), argOrdinal0);
    final RelDataType argOrdinalType1 = getFieldType(oldAggRel.getInput(), argOrdinal1);

    final RelDataType oldCallType =
        typeFactory.createTypeWithNullability(oldCall.getType(),
            argOrdinalType0.isNullable() || argOrdinalType1.isNullable());

    final RexNode arg0Ref =
        rexBuilder.ensureType(oldCallType, inputExprs.get(argOrdinal0), true);
    final RexNode arg1Ref =
        rexBuilder.ensureType(oldCallType, inputExprs.get(argOrdinal1), true);

    RexNode covarPop = getCovarianceNode(oldAggRel, oldCall, true, false,
        newCalls, aggCallMapping, oldCallType, arg0Ref, arg0Ref, inputExprs);
    RexNode stddevPop0 = getCovarianceNode(oldAggRel, oldCall, true, true,
        newCalls, aggCallMapping, oldCallType, arg0Ref, arg0Ref, inputExprs);
    RexNode stddevPop1 = getCovarianceNode(oldAggRel, oldCall, true, true,
        newCalls, aggCallMapping, oldCallType, arg1Ref, arg1Ref, inputExprs);
    final RexNode denominator =
        rexBuilder.makeCall(SqlStdOperatorTable.MULTIPLY, stddevPop0, stddevPop1);
    return rexBuilder.makeCast(oldCallType,
        rexBuilder.makeCall(SqlStdOperatorTable.DIVIDE, covarPop, denominator));
  }

  private RexNode reduceCovariance(
      Aggregate oldAggRel,
      AggregateCall oldCall,
      boolean biased,
      boolean sqrt,
      List<AggregateCall> newCalls,
      Map<AggregateCall, RexNode> aggCallMapping,
      List<RexNode> inputExprs) {
    // covar_pop(x, y) ==>
    //   power(
    //     (sum(x * x) - sum(x) * sum(x) / count(x))
    //     / count(x),
    //     .5)
    //
    // stddev_samp(x) ==>
    //   power(
    //     (sum(x * x) - sum(x) * sum(x) / count(x))
    //     / nullif(count(x) - 1, 0),
    //     .5)
    final RelOptCluster cluster = oldAggRel.getCluster();
    final RexBuilder rexBuilder = cluster.getRexBuilder();
    final RelDataTypeFactory typeFactory = cluster.getTypeFactory();

    assert oldCall.getArgList().size() == 2 : oldCall.getArgList();
    final int arg0Ordinal = oldCall.getArgList().get(0);
    final int arg1Ordinal = oldCall.getArgList().get(1);
    final RelDataType arg0OrdinalType = getFieldType(oldAggRel.getInput(), arg0Ordinal);
    final RelDataType arg1OrdinalType = getFieldType(oldAggRel.getInput(), arg1Ordinal);
    final RelDataType oldCallType =
        typeFactory.createTypeWithNullability(oldCall.getType(),
            arg0OrdinalType.isNullable() || arg1OrdinalType.isNullable());

    final RexNode arg0Ref =
        rexBuilder.ensureType(oldCallType, inputExprs.get(arg0Ordinal), true);
    final RexNode arg1Ref =
        rexBuilder.ensureType(oldCallType, inputExprs.get(arg1Ordinal), true);

    RexNode result = getCovarianceNode(oldAggRel, oldCall, biased, sqrt, newCalls, aggCallMapping,
        oldCallType, arg0Ref, arg1Ref, inputExprs);
    return rexBuilder.makeCast(oldCall.getType(), result);
  }

  /**
   * Finds the ordinal of an element in a list, or adds it.
   *
   * @param list    List
   * @param element Element to lookup or add
   * @param <T>     Element type
   * @return Ordinal of element in list
   */
  private static <T> int lookupOrAdd(List<T> list, T element) {
    int ordinal = list.indexOf(element);
    if (ordinal == -1) {
      ordinal = list.size();
      list.add(element);
    }
    return ordinal;
  }

  /**
   * Do a shallow clone of oldAggRel and update aggCalls. Could be refactored
   * into Aggregate and subclasses - but it's only needed for some
   * subclasses.
   *
   * @param relBuilder Builder of relational expressions; at the top of its
   *                   stack is its input
   * @param oldAggregate LogicalAggregate to clone.
   * @param newCalls  New list of AggregateCalls
   */
  protected void newAggregateRel(RelBuilder relBuilder,
      Aggregate oldAggregate,
      List<AggregateCall> newCalls) {
    relBuilder.aggregate(
        relBuilder.groupKey(oldAggregate.getGroupSet(),
            oldAggregate.getGroupSets()),
        newCalls);
  }

  /**
   * Add a calc with the expressions to compute the original agg calls from the
   * decomposed ones.
   *
   * @param relBuilder Builder of relational expressions; at the top of its
   *                   stack is its input
   * @param rowType The output row type of the original aggregate.
   * @param exprs The expressions to compute the original agg calls.
   */
  protected void newCalcRel(RelBuilder relBuilder,
      RelDataType rowType,
      List<RexNode> exprs) {
    relBuilder.project(exprs, rowType.getFieldNames());
  }

  private RelDataType getFieldType(RelNode relNode, int i) {
    final RelDataTypeField inputField =
        relNode.getRowType().getFieldList().get(i);
    return inputField.getType();
  }
}

// End AggregateReduceFunctionsRule.java
