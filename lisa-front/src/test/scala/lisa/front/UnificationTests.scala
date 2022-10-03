package lisa.front

import lisa.front.fol.FOL.LabelType
import lisa.front.fol.FOL.WithArityType
import lisa.front.printer.FrontPositionedPrinter
import lisa.front.printer.FrontPrintStyle
import lisa.front.{*, given}
import org.scalatest.Ignore
import org.scalatest.funsuite.AnyFunSuite

import scala.language.adhocExtensions

@Ignore
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

  test("same boolean constant") {
    checkUnifiesAs(a, a)(emptyResult)
  }
  test("different boolean constants") {
    checkDoesNotUnify(a, b)
  }
  test("boolean and schematic constants") {
    checkDoesNotUnify(a, sa)
  }
  test("boolean constant expression") {
    checkUnifiesAs(a /\ b, a /\ b)(emptyResult)
  }

  test("schematic boolean constant") {
    checkUnifiesAs(sa, a)(emptyResult + AssignedPredicate(sa, a))
  }
  test("same schematic boolean constant") {
    checkUnifiesAs(sa, sa)(emptyResult + AssignedPredicate(sa, sa))
  }
  test("expression with schematic boolean constant") {
    checkUnifiesAs(sa /\ b, a /\ b)(emptyResult + AssignedPredicate(sa, a))
  }
  test("expression with multiple schematic boolean constants") {
    checkUnifiesAs(sa /\ sb, a /\ b)(emptyResult + AssignedPredicate(sa, a) + AssignedPredicate(sb, b))
  }
  test("matching two schematic boolean constants") {
    checkUnifiesAs(sa /\ b, sb /\ b)(emptyResult + AssignedPredicate(sa, sb))
  }
  test("schematic boolean constants match expressions") {
    checkUnifiesAs(sa /\ sb, (a ==> b) /\ (c \/ a))(emptyResult + AssignedPredicate(sa, a ==> b) + AssignedPredicate(sb, c \/ a))
  }
  test("schematic predicate matches same expressions") {
    checkUnifiesAs(sa /\ sa, b /\ b)(emptyResult + AssignedPredicate(sa, b))
  }
  test("schematic predicate matches equivalent expressions") {
    checkUnifiesAs(sa /\ sa, (a \/ b) /\ (b \/ a))(emptyResult + AssignedPredicate(sa, a \/ b))
  }
  test("schematic predicate does not match different constants") {
    checkDoesNotUnify(sa /\ sa, a /\ b)
  }
  test("schematic 0-ary predicate: equivalent expression in the context") {
    checkUnifiesAs(sa, a /\ b, emptyContext + AssignedPredicate(sa, b /\ a))(
      emptyResult + AssignedPredicate(sa, b /\ a)
    )
  }
  test("schematic 0-ary predicate with partial mapping") {
    checkUnifiesAs(sa, a, emptyContext + AssignedPredicate(sa, a))(emptyResult + AssignedPredicate(sa, a))
  }
  test("schematic 0-ary predicate with contradicting partial mapping") {
    checkDoesNotUnify(sa, a, emptyContext + AssignedPredicate(sa, b))
  }
  test("schematic 0-ary predicate with contradicting partial mapping 2") {
    checkDoesNotUnify(sa, a, emptyContext + AssignedPredicate(sb, a))
  }

  test("same predicate") {
    checkUnifiesAs(p1(t), p1(t))(emptyResult)
  }
  test("predicate of schematic variable to predicate of constant") {
    checkUnifiesAs(p1(st), p1(u))(emptyResult + AssignedFunction(st, u))
  }
  test("schematic to constant predicate") {
    checkUnifiesAs(sp1(t), p1(t))(emptyResult + AssignedPredicate(sp1, LambdaPredicate(x => p1(x))))
  }
  test("schematic predicate to expression") {
    checkUnifiesAs(sp1(t), p1(t) /\ p1(u))(emptyResult + AssignedPredicate(sp1, LambdaPredicate(x => p1(x) /\ p1(u))))
  }
  test("schematic connector of boolean constant to boolean constant") {
    checkUnifiesAs(sg1(a), b)(emptyResult + AssignedConnector(sg1, LambdaConnector(_ => b)))
  }
  test("schematic connector of schematic boolean constant does not match boolean constant") {
    checkDoesNotUnify(sg1(sa), a)
  }
  test("schematic connector of schematic boolean constant with partial mapping of connector") {
    checkUnifiesAs(sg1(sa), b, emptyContext + AssignedConnector(sg1, LambdaConnector(x => x)))(
      emptyResult +
        AssignedConnector(sg1, LambdaConnector(x => x)) + AssignedPredicate(sa, b)
    )
  }
  test("schematic connector of schematic boolean constant with partial mapping of 0-ary predicate") {
    checkUnifiesAs(sg1(sa), b, emptyContext + AssignedPredicate(sa, b))(
      emptyResult + AssignedPredicate(sa, b) +
        AssignedConnector(sg1, LambdaConnector(x => x))
    )
  }
  test("schematic connector of schematic boolean constant with partial mapping of connector and 0-ary predicate") {
    checkUnifiesAs(sg1(sa), b, emptyContext + AssignedConnector(sg1, LambdaConnector(x => x)) + AssignedPredicate(sa, b))(
      emptyContext + AssignedConnector(sg1, LambdaConnector(x => x)) + AssignedPredicate(sa, b)
    )
  }
  test("schematic connector of schematic boolean constant with partial mapping of connector and different 0-ary predicate") {
    checkDoesNotUnify(sg1(sa), b, emptyContext + AssignedConnector(sg1, LambdaConnector(x => x)) + AssignedPredicate(sa, a))
  }
  test("schematic connector of schematic boolean constant with partial mapping of 0-ary predicate and different connector") {
    checkDoesNotUnify(sg1(sa), b, emptyContext + AssignedConnector(sg1, LambdaConnector(_ => a)) + AssignedPredicate(sa, b))
  }
  test("predicate of a variable") {
    checkUnifiesAs(p1(x), p1(x))(emptyResult + (x -> x))
  }
  test("predicate of a variable to a predicate of a different variable") {
    checkUnifiesAs(p1(x), p1(y))(emptyResult + (x -> y))
  }
  test("predicate of a variable to a predicate of a different variable with partial mapping of variables") {
    checkUnifiesAs(p1(x), p1(y), emptyContext + (x -> y))(emptyResult + (x -> y))
  }
  test("predicate of a variable to a predicate of a different variable with incompatible partial mapping of variables") {
    checkDoesNotUnify(p1(x), p1(y), emptyContext + (x -> z))
  }

  test("exists constant") {
    checkUnifiesAs(exists(x, a), exists(x, a))(emptyResult + (x -> x))
  }
  test("exists constant with different bound variables") {
    checkUnifiesAs(exists(x, a), exists(y, a))(emptyResult + (x -> y))
  }
  test("exists expression with different bound variables") {
    checkUnifiesAs(exists(x, p1(x)), exists(y, p1(y)))(emptyResult + (x -> y))
  }
  test("exists expression of bound vs free variable") {
    checkDoesNotUnify(exists(x, p1(x)), exists(y, p1(z)))
  }
  test("exists schematic predicate to exists expression") {
    checkUnifiesAs(exists(x, sp1(x)), exists(y, p1(y) /\ a))(emptyResult + (x -> y) + AssignedPredicate(sp1, LambdaPredicate(v => p1(v) /\ a)))
  }
  test("exists schematic boolean constant to exists predicate") {
    checkUnifiesAs(exists(x, sa), exists(x, p1(t)))(emptyResult + (x -> x) + AssignedPredicate(sa, p1(t)))
  }
  test("exists schematic boolean constant to exists unary predicate (does not unify)") {
    checkDoesNotUnify(exists(x, sa), exists(x, p1(x)))
  }
  test("exists schematic unary predicate to exists unary predicate with incompatible predicate mapping") {
    checkDoesNotUnify(exists(x, sp1(x)), exists(x, p1(x)), emptyContext + (x -> x) + AssignedPredicate(sp1, LambdaPredicate(_ => p1(x))))
  }
  test("exists expression: switch bound and free variable") {
    checkUnifiesAs(exists(x, exists(y, p1(x) /\ p1(y))), exists(y, exists(x, p1(y) /\ p1(x))))(
      emptyResult + (x -> y) + (y -> x)
    )
  }

  test("term with different schematic variables to a term with the same variable") {
    checkUnifiesAs(p1(st) /\ p1(su), p1(x) /\ p1(x))(emptyResult + AssignedFunction(st, x) + AssignedFunction(su, x))
  }
  test("term with same schematic variable to a term with different variables (does not unify)") {
    checkDoesNotUnify(p1(st) /\ p1(st), p1(x) /\ p1(y))
  }
  test("term with same schematic variable to a term with different schematic variables (does not unify)") {
    checkDoesNotUnify(p1(st) /\ p1(st), p1(su) /\ p1(sv))
  }
  test("rename schematic variable") {
    checkUnifiesAs(p1(st) /\ p1(st), p1(su) /\ p1(su))(emptyResult + AssignedFunction(st, su))
  }
}
