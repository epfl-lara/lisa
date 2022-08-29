package lisa.front

import lisa.front.fol.FOL.LabelType
import lisa.front.fol.FOL.WithArityType
import lisa.front.printer.FrontPositionedPrinter
import lisa.front.printer.FrontPrintStyle
import lisa.front.{*, given}
import org.scalatest.funsuite.AnyFunSuite

import scala.language.adhocExtensions

class UnificationTests extends AnyFunSuite {

  val (sa, sb, sc) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))
  val (a, b, c) = (ConstantPredicateLabel[0]("a"), ConstantPredicateLabel[0]("b"), ConstantPredicateLabel[0]("c"))

  val (st, su, sv) = (SchematicTermLabel[0]("t"), SchematicTermLabel[0]("u"), SchematicTermLabel[0]("v"))
  val (t, u, v) = (ConstantFunctionLabel[0]("t"), ConstantFunctionLabel[0]("u"), ConstantFunctionLabel[0]("v"))

  val (sf1, f1) = (SchematicTermLabel[1]("f1"), ConstantFunctionLabel[1]("f1"))
  val (sg1) = (SchematicConnectorLabel[1]("g1"))
  val (sp1, p1) = (SchematicPredicateLabel[1]("p1"), ConstantPredicateLabel[1]("p1"))

  val (x, y, z) = (VariableLabel("x"), VariableLabel("y"), VariableLabel("z"))

  def unify(pattern: Formula, target: Formula, partial: UnificationContext = emptyContext): Option[(IndexedSeq[Sequent], UnificationContext)] =
    unifyAndResolve(
      IndexedSeq(PartialSequent(IndexedSeq(pattern), IndexedSeq.empty)),
      IndexedSeq(Sequent(IndexedSeq(target), IndexedSeq.empty)),
      IndexedSeq.empty,
      partial,
      IndexedSeq((IndexedSeq(0), IndexedSeq.empty))
    )

  @deprecated
  def checkUnifies(pattern: Formula, target: Formula, partial: UnificationContext = emptyContext): Unit = {
    assert(
      unify(pattern, target, partial).nonEmpty,
      s"Pattern ${FrontPositionedPrinter.prettyFormula(pattern, symbols = FrontPrintStyle.Unicode)} and " +
        s"target ${FrontPositionedPrinter.prettyFormula(target, symbols = FrontPrintStyle.Unicode)} did not unify"
    )
  }

  def checkDoesNotUnify(pattern: Formula, target: Formula, partial: UnificationContext = emptyContext): Unit = {
    assert(
      unify(pattern, target, partial).isEmpty,
      s"Pattern ${FrontPositionedPrinter.prettyFormula(pattern, symbols = FrontPrintStyle.Unicode)} and " +
        s"target ${FrontPositionedPrinter.prettyFormula(target, symbols = FrontPrintStyle.Unicode)} did unify"
    )
  }

  def contextsEqual(ctx1: UnificationContext, ctx2: UnificationContext): Boolean = {
    def names(lambda: WithArityType[?]): Seq[String] = (0 until lambda.arity).map(i => s"unique_name_$i")
    def normalizeFunction[N <: Arity](lambda: LambdaFunction[N]) = {
      val newParams = names(lambda).map(SchematicTermLabel.apply[0])
      LambdaFunction.unsafe(
        newParams,
        instantiateTermSchemas(lambda.body, lambda.parameters.zip(newParams).map { case (l1, l2) => RenamedLabel.unsafe(l1, l2).toAssignment })
      )
    }
    // val x:Nothing = normalizeFunction
    def normalizePredicate(lambda: LambdaPredicate[?]): LambdaPredicate[?] = {
      val newParams = names(lambda).map(SchematicTermLabel.apply[0])
      LambdaPredicate.unsafe(
        newParams,
        instantiateFormulaSchemas(lambda.body, lambda.parameters.zip(newParams).map { case (l1, l2) => RenamedLabel.unsafe(l1, l2).toAssignment }, Seq.empty, Seq.empty)
      )
    }
    def normalizeConnector(lambda: LambdaConnector[?]): LambdaConnector[?] = {
      val newParams = names(lambda).map(SchematicPredicateLabel.apply[0])
      LambdaConnector.unsafe(
        newParams,
        instantiateFormulaSchemas(lambda.body, Seq.empty, lambda.parameters.zip(newParams).map { case (l1, l2) => RenamedLabel.unsafe(l1, l2).toAssignment }, Seq.empty)
      )
    }
    def normalizeContext(ctx: UnificationContext): UnificationContext =
      UnificationContext(
        ctx.predicates.view.mapValues(normalizePredicate).toMap,
        ctx.functions.view.mapValues(normalizeFunction).toMap,
        ctx.connectors.view.mapValues(normalizeConnector).toMap,
        ctx.variables
      )
    normalizeContext(ctx1) == normalizeContext(ctx2)
  }

  def checkUnifiesAs(pattern: Formula, target: Formula, partial: UnificationContext)(expected: UnificationContext): Unit = {
    unify(pattern, target, partial) match {
      case Some((_, resultCtx)) => assert(contextsEqual(resultCtx, expected), resultCtx)
      case None =>
        fail(
          s"Pattern ${FrontPositionedPrinter.prettyFormula(pattern, symbols = FrontPrintStyle.Unicode)} and " +
            s"target ${FrontPositionedPrinter.prettyFormula(target, symbols = FrontPrintStyle.Unicode)} did not unify"
        )
    }
  }

  def checkUnifiesAs(pattern: Formula, target: Formula)(expected: UnificationContext): Unit =
    checkUnifiesAs(pattern, target, emptyContext)(expected)

  val emptyContext: UnificationContext = UnificationContext()
  val emptyResult: UnificationContext = UnificationContext()

  test("boolean constant") {
    checkUnifiesAs(a, a)(emptyResult)
    checkDoesNotUnify(a, b)
    checkDoesNotUnify(a, sa)
    checkUnifiesAs(a /\ b, a /\ b)(emptyResult)
  }

  test("schematic boolean constant") {
    checkUnifiesAs(sa, a)(emptyResult + AssignedPredicate(sa, a))
    checkUnifiesAs(sa, sa)(emptyResult + AssignedPredicate(sa, sa))
    checkUnifiesAs(sa /\ b, a /\ b)(emptyResult + AssignedPredicate(sa, a))
    checkUnifiesAs(sa /\ sb, a /\ b)(emptyResult + AssignedPredicate(sa, a) + AssignedPredicate(sb, b))
    checkUnifiesAs(sa /\ b, sb /\ b)(emptyResult + AssignedPredicate(sa, sb))
    checkUnifiesAs(sa /\ sb, (a ==> b) /\ (c \/ a))(emptyResult + AssignedPredicate(sa, a ==> b) + AssignedPredicate(sb, c \/ a))
    checkUnifiesAs(sa /\ sa, b /\ b)(emptyResult + AssignedPredicate(sa, b))
    checkUnifiesAs(sa /\ sa, (a \/ b) /\ (b \/ a))(emptyResult + AssignedPredicate(sa, a \/ b))
    checkDoesNotUnify(sa /\ sa, a /\ b)

    checkUnifiesAs(sa, a /\ b, emptyContext + AssignedPredicate(sa, b /\ a))(
      emptyResult + AssignedPredicate(
        sa,
        b /\
          a
      )
    )
    checkUnifiesAs(sa, a, emptyContext + AssignedPredicate(sa, a))(emptyResult + AssignedPredicate(sa, a))
    checkDoesNotUnify(sa, a, emptyContext + AssignedPredicate(sa, b))
    checkDoesNotUnify(sa, a, emptyContext + AssignedPredicate(sb, a))
  }

  test("schematic predicate") {
    checkUnifiesAs(p1(t), p1(t))(emptyResult)
    checkUnifiesAs(p1(st), p1(u))(emptyResult + AssignedFunction(st, u))
    checkUnifiesAs(sp1(t), p1(t))(emptyResult + AssignedPredicate(sp1, LambdaPredicate(x => p1(x))))
    checkUnifiesAs(sp1(t), p1(t) /\ p1(u))(emptyResult + AssignedPredicate(sp1, LambdaPredicate(x => p1(x) /\ p1(u))))

    checkUnifiesAs(sg1(a), b)(emptyResult + AssignedConnector(sg1, LambdaConnector(_ => b)))
    checkDoesNotUnify(sg1(sa), a)
    checkUnifiesAs(sg1(sa), b, emptyContext + AssignedConnector(sg1, LambdaConnector(x => x)))(
      emptyResult +
        AssignedConnector(sg1, LambdaConnector(x => x)) + AssignedPredicate(sa, b)
    )
    checkUnifiesAs(sg1(sa), b, emptyContext + AssignedPredicate(sa, b))(
      emptyResult + AssignedPredicate(sa, b) +
        AssignedConnector(sg1, LambdaConnector(x => x))
    )

    checkUnifiesAs(sg1(sa), b, emptyContext + AssignedConnector(sg1, LambdaConnector(x => x)) + AssignedPredicate(sa, b))(
      emptyContext + AssignedConnector(sg1, LambdaConnector(x => x)) + AssignedPredicate(sa, b)
    )
    checkDoesNotUnify(sg1(sa), b, emptyContext + AssignedConnector(sg1, LambdaConnector(x => x)) + AssignedPredicate(sa, a))
    checkDoesNotUnify(sg1(sa), b, emptyContext + AssignedConnector(sg1, LambdaConnector(_ => a)) + AssignedPredicate(sa, b))

    checkUnifiesAs(p1(x), p1(x))(emptyResult + (x -> x))
    checkUnifiesAs(p1(x), p1(y))(emptyResult + (x -> y))
    checkUnifiesAs(p1(x), p1(y), emptyContext + (x -> y))(emptyResult + (x -> y))
    checkDoesNotUnify(p1(x), p1(y), emptyContext + (x -> z))
  }

  test("exists") {
    checkUnifiesAs(exists(x, a), exists(x, a))(emptyResult + (x -> x))
    checkUnifiesAs(exists(x, a), exists(y, a))(emptyResult + (x -> y))
    checkUnifiesAs(exists(x, p1(x)), exists(y, p1(y)))(emptyResult + (x -> y))
    checkDoesNotUnify(exists(x, p1(x)), exists(y, p1(z)))

    checkUnifiesAs(exists(x, sp1(x)), exists(y, p1(y) /\ a))(emptyResult + (x -> y) + AssignedPredicate(sp1, LambdaPredicate(v => p1(v) /\ a)))
    checkUnifiesAs(exists(x, sa), exists(x, p1(t)))(emptyResult + (x -> x) + AssignedPredicate(sa, p1(t)))
    checkDoesNotUnify(exists(x, sa), exists(x, p1(x)))
    checkDoesNotUnify(exists(x, sp1(x)), exists(x, p1(x)), emptyContext + (x -> x) + AssignedPredicate(sp1, LambdaPredicate(_ => p1(x))))

    checkUnifiesAs(exists(x, exists(y, p1(x) /\ p1(y))), exists(y, exists(x, p1(y) /\ p1(x))))(
      emptyResult + (x -> y)
        + (y -> x)
    )
  }

  test("schematic predicate expressions") {
    checkUnifiesAs(p1(st) /\ p1(su), p1(x) /\ p1(x))(emptyResult + AssignedFunction(st, x) + AssignedFunction(su, x))
    checkDoesNotUnify(p1(st) /\ p1(st), p1(x) /\ p1(y))
    checkDoesNotUnify(p1(st) /\ p1(st), p1(su) /\ p1(sv))
    checkUnifiesAs(p1(st) /\ p1(st), p1(su) /\ p1(su))(emptyResult + AssignedFunction(st, su))
  }
}
