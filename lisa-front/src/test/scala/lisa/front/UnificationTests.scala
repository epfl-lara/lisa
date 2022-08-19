package lisa.front

import org.scalatest.funsuite.AnyFunSuite
import scala.language.adhocExtensions

import lisa.front.fol.FOL.{LabelType, WithArityType}
import lisa.front.{*, given}

class UnificationTests extends AnyFunSuite {

  val (sa, sb, sc) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))
  val (a, b, c) = (ConstantPredicateLabel[0]("a"), ConstantPredicateLabel[0]("b"), ConstantPredicateLabel[0]("c"))

  val (st, su, sv) = (SchematicTermLabel[0]("t"), SchematicTermLabel[0]("u"), SchematicTermLabel[0]("v"))
  val (t, u, v) = (ConstantFunctionLabel[0]("t"), ConstantFunctionLabel[0]("u"), ConstantFunctionLabel[0]("v"))

  val (sf1, f1) = (SchematicTermLabel[1]("f1"), ConstantFunctionLabel[1]("f1"))
  val (sg1) = (SchematicConnectorLabel[1]("g1"))
  val (sp1, p1) = (SchematicPredicateLabel[1]("p1"), ConstantPredicateLabel[1]("p1"))

  val (x, y, z) = (VariableLabel("x"), VariableLabel("y"), VariableLabel("z"))

  def unify(pattern: Formula, target: Formula, partial: UnificationContext = UnificationContext()): Option[(IndexedSeq[Sequent], UnificationContext)] =
    unifyAndResolve(
      IndexedSeq(PartialSequent(IndexedSeq(pattern), IndexedSeq.empty)),
      IndexedSeq(Sequent(IndexedSeq(target), IndexedSeq.empty)),
      IndexedSeq.empty,
      partial,
      IndexedSeq((IndexedSeq(0), IndexedSeq.empty))
    )

  @deprecated
  def checkUnifies(pattern: Formula, target: Formula, partial: UnificationContext = UnificationContext()): Unit = {
    assert(unify(pattern, target, partial).nonEmpty, "It did not unify")
  }

  def checkDoesNotUnify(pattern: Formula, target: Formula, partial: UnificationContext = UnificationContext()): Unit = {
    assert(unify(pattern, target, partial).isEmpty, "It did unify")
  }

  def contextsEqual(ctx1: UnificationContext, ctx2: UnificationContext): Boolean = {
    def names(lambda: WithArityType[?]): Seq[String] = (0 until lambda.arity).map(i => s"unique_name_$i")
    def normalizeFunction[N<:Arity](lambda: LambdaFunction[N]) = {
      val newParams = names(lambda).map(SchematicTermLabel.apply[0])
      LambdaFunction.unsafe(
        newParams,
        instantiateTermSchemas(lambda.body, lambda.parameters.zip(newParams).map { case (l1, l2) => RenamedLabel.unsafe(l1, l2).toAssignment })
      )
    }
    //val x:Nothing = normalizeFunction
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
        ctx.variables,
      )
    normalizeContext(ctx1) == normalizeContext(ctx2)
  }

  def checkUnifiesAs(pattern: Formula, target: Formula, partial: UnificationContext, ctx: UnificationContext): Unit = {
    unify(pattern, target, partial) match {
      case Some((_, resultCtx)) => assert(contextsEqual(resultCtx, ctx), resultCtx)
      case None => throw new AssertionError("It did not unify")
    }
  }

  def checkUnifiesAs(pattern: Formula, target: Formula, ctx: UnificationContext): Unit =
    checkUnifiesAs(pattern, target, UnificationContext(), ctx)

  val U: UnificationContext = UnificationContext()

  test("unification 2") {
    checkUnifiesAs(a, a, UnificationContext())
    checkDoesNotUnify(a, b)
    checkDoesNotUnify(a, sa)
    checkUnifiesAs(a /\ b, a /\ b, U)

    checkUnifiesAs(sa, a, U + AssignedPredicate(sa, a))
    checkUnifiesAs(sa, sa, U + AssignedPredicate(sa, sa))
    checkUnifiesAs(sa /\ b, a /\ b, U + AssignedPredicate(sa, a))
    checkUnifiesAs(sa /\ sb, a /\ b, U + AssignedPredicate(sa, a) + AssignedPredicate(sb, b))
    checkUnifiesAs(sa /\ b, sb /\ b, U + AssignedPredicate(sa, sb))
    checkUnifiesAs(sa /\ sb, (a ==> b) /\ (c \/ a), U + AssignedPredicate(sa, a ==> b) + AssignedPredicate(sb, c \/ a))
    checkUnifiesAs(sa /\ sa, b /\ b, U + AssignedPredicate(sa, b))
    checkUnifiesAs(sa /\ sa, (a \/ b) /\ (b \/ a), U + AssignedPredicate(sa, a \/ b))
    checkDoesNotUnify(sa /\ sa, a /\ b)

    checkUnifiesAs(sa, a /\ b, U + AssignedPredicate(sa, b /\ a), U + AssignedPredicate(sa, b /\ a))
    checkUnifiesAs(sa, a, U + AssignedPredicate(sa, a), U + AssignedPredicate(sa, a))
    checkDoesNotUnify(sa, a, U + AssignedPredicate(sa, b))
    checkDoesNotUnify(sa, a, U + AssignedPredicate(sb, a))

    checkUnifiesAs(p1(t), p1(t), U)
    checkUnifiesAs(p1(st), p1(u), U + AssignedFunction(st, u))
    checkUnifiesAs(sp1(t), p1(t), U + AssignedPredicate(sp1, LambdaPredicate(x => p1(x))))
    checkUnifiesAs(sp1(t), p1(t) /\ p1(u), U + AssignedPredicate(sp1, LambdaPredicate(x => p1(x) /\ p1(u))))

    checkUnifiesAs(sg1(a), b, U + AssignedConnector(sg1, LambdaConnector(_ => b)))
    checkDoesNotUnify(sg1(sa), a)
    checkUnifiesAs(sg1(sa), b, U + AssignedConnector(sg1, LambdaConnector(x => x)), U + AssignedConnector(sg1, LambdaConnector(x => x)) + AssignedPredicate(sa, b))
    checkUnifiesAs(sg1(sa), b, U + AssignedPredicate(sa, b), U + AssignedPredicate(sa, b) + AssignedConnector(sg1, LambdaConnector(x => x)))

    checkUnifiesAs(sg1(sa), b, U + AssignedConnector(sg1, LambdaConnector(x => x)) + AssignedPredicate(sa, b), U + AssignedConnector(sg1, LambdaConnector(x => x)) + AssignedPredicate(sa, b))
    checkDoesNotUnify(sg1(sa), b, U + AssignedConnector(sg1, LambdaConnector(x => x)) + AssignedPredicate(sa, a))
    checkDoesNotUnify(sg1(sa), b, U + AssignedConnector(sg1, LambdaConnector(_ => a)) + AssignedPredicate(sa, b))

    checkUnifiesAs(exists(x, a), exists(x, a), U + (x -> x))
    checkUnifiesAs(exists(x, a), exists(y, a), U + (x -> y))
    checkUnifiesAs(exists(x, p1(x)), exists(y, p1(y)), U + (x -> y))
    checkDoesNotUnify(exists(x, p1(x)), exists(y, p1(z)))
    checkUnifiesAs(p1(x), p1(x), U + (x -> x))
    checkUnifiesAs(p1(x), p1(y), U + (x -> y))
    checkUnifiesAs(p1(x), p1(y), U + (x -> y), U + (x -> y))
    checkDoesNotUnify(p1(x), p1(y), U + (x -> z))

    checkUnifiesAs(exists(x, sp1(x)), exists(y, p1(y) /\ a), U + (x -> y) + AssignedPredicate(sp1, LambdaPredicate(v => p1(v) /\ a)))
    checkUnifiesAs(exists(x, sa), exists(x, p1(t)), U + (x -> x) + AssignedPredicate(sa, p1(t)))
    checkDoesNotUnify(exists(x, sa), exists(x, p1(x)))
    checkDoesNotUnify(exists(x, sp1(x)), exists(x, p1(x)), U + (x -> x) + AssignedPredicate(sp1, LambdaPredicate(_ => p1(x))))

    checkUnifiesAs(p1(st) /\ p1(su), p1(x) /\ p1(x), U + AssignedFunction(st, x) + AssignedFunction(su, x))
    checkDoesNotUnify(p1(st) /\ p1(st), p1(x) /\ p1(y))
    checkDoesNotUnify(p1(st) /\ p1(st), p1(su) /\ p1(sv))
    checkUnifiesAs(p1(st) /\ p1(st), p1(su) /\ p1(su), U + AssignedFunction(st, su))

    checkUnifiesAs(exists(x, exists(y, p1(x) /\ p1(y))), exists(y, exists(x, p1(y) /\ p1(x))), U + (x -> y) + (y -> x))
  }
}
