package lisa.proven.mathematics

import lisa.automation.kernel.SimplePropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.proven.mathematics.SetTheory
import lisa.utils.Helpers.<=>
import lisa.utils.Library
import lisa.utils.Printer
import lisa.utils.tactics.BasicStepTactic.InstFunSchema
import lisa.utils.tactics.SimpleDeducedSteps

import scala.collection.immutable.Map
import scala.collection.immutable.Seq
import scala.collection.immutable.Set
object Mapping extends lisa.Main {

  val x: VariableLabel = variable
  val y: VariableLabel = variable
  val z: VariableLabel = variable
  val h: VariableFormulaLabel = formulaVariable

  val functionalMapping = makeTHM("∀ 'a. elem('a, 'A) ⇒ (∃! 'x. 'phi('x, 'a)) ⊢ ∃! 'X. ∀ 'x. elem('x, 'X) ↔ (∃ 'a. elem('a, 'A) ∧ 'phi('x, 'a))") {
    val a: VariableLabel = VariableLabel("a")
    val b: VariableLabel = variable

    val f = variable
    val A = variable
    val X = variable
    val B = variable
    val B1 = variable
    val phi: SchematicPredicateLabel = predicate(2)
    val P: SchematicPredicateLabel = predicate(2)
    val P2 = SchematicPredicateLabel("P", 3)

    val H = existsOne(x, phi(x, a))
    val H1 = forall(a, in(a, A) ==> existsOne(x, phi(x, a)))

    have((H) |- in(a, A) ==> existsOne(x, phi(x, a))) by Trivial
    val s3 = have(H1 |- H1) by Hypothesis
    val s = instantiatePredicateSchemas(ax"replacementSchema", Map(P2 -> LambdaTermFormula(Seq(a, x, y), phi(x, a))))
    val p0 = have(" ⊢ (∀'x. elem('x, 'A) ⇒ (∃!'y. 'phi('y, 'x))) ⇒ (∃'B. ∀'x. elem('x, 'A) ⇒ (∃'y. elem('y, 'B) ∧ 'phi('y, 'x)))") by InstPredSchema(
      Map(P2 -> LambdaTermFormula(Seq(a, x, y), phi(y, x)))
    )(ax"replacementSchema")

    val s5 = andThen("(∀'x. elem('x, 'A) ⇒ (∃!'y. 'phi('y, 'x))) ⊢ (∃'B. ∀'x. elem('x, 'A) ⇒ (∃'y. elem('y, 'B) ∧ 'phi('y, 'x)))") by Rewrite
    val s6 = andThen(H1 |- exists(B, forall(a, in(a, A) ==> exists(y, in(y, B) /\ (phi(y, a)))))) by InstFunSchema(
      Map(
        x -> LambdaTermTerm(Nil, a),
        y -> LambdaTermTerm(Nil, x)
      )
    )
    // have((H1) |- exists(B, forall(x, in(x, A) ==> exists(y, in(y, B) /\ (phi(y, x)))) ))by Cut.withParameters(H1)(s3, s5) // ⊢ ∃B. ∀x. (x ∈ A) ⇒ ∃y. (y ∈ B) ∧ (y = (x, b))
    // val s6 = andThen(H1 |- exists(B, forall(a, in(a, A) ==> exists(y, in(y, B) /\ (phi(y, a)))))) by RightExists.withParameters(forall(a, in(a, A) ==> exists(y, in(y, B) /\ (phi(y, a)))), B, B)
    val q0 = have(() |- exists(y, forall(x, in(x, y) <=> (in(x, z) /\ exists(a, in(a, A) /\ phi(x, a)))))) by InstPredSchema(
      Map(P -> LambdaTermFormula(Seq(x, z), exists(a, in(a, A) /\ phi(x, a))))
    )(ax"comprehensionSchema")
    val s7 = andThen(() |- exists(y, forall(x, in(x, y) <=> (in(x, B) /\ exists(a, in(a, A) /\ phi(x, a)))))) by InstFunSchema(Map(z -> LambdaTermTerm(Seq(), B)))

    val s8 = have(Set(forall(a, in(a, A) ==> existsOne(x, phi(x, a))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), exists(a, phi(x, a) /\ in(a, A))) |- in(x, B)) subproof {
      val y1 = variable
      have(in(y1, B) |- in(y1, B)) by Hypothesis
      andThen((in(y1, B), x === y1) |- in(x, B)) by RightSubstEq(List((x, y1)), LambdaTermFormula(Seq(f), in(f, B)))
      andThen(Set(in(y1, B), (x === y1) <=> phi(x, a), phi(x, a)) |- in(x, B)) by LeftSubstIff(List(((x === y1), phi(x, a))), LambdaFormulaFormula(Seq(h), h()))
      andThen(Set(y === y1, in(y1, B), (x === y) <=> phi(x, a), phi(x, a)) |- in(x, B)) by LeftSubstEq(List((y, y1)), LambdaTermFormula(Seq(f), (x === f) <=> phi(x, a)))
      andThen(Set((y === y1) <=> phi(y1, a), phi(y1, a), in(y1, B), (x === y) <=> phi(x, a), phi(x, a)) |- in(x, B)) by LeftSubstIff(List((phi(y1, a), y1 === y)), LambdaFormulaFormula(Seq(h), h()))
      andThen(Set(forall(x, (y === x) <=> phi(x, a)), phi(y1, a), in(y1, B), (x === y) <=> phi(x, a), phi(x, a)) |- in(x, B)) by LeftForall.withParameters((y === x) <=> phi(x, a), x, y1)
      andThen(Set(forall(x, (y === x) <=> phi(x, a)), phi(y1, a), in(y1, B), phi(x, a)) |- in(x, B)) by LeftForall.withParameters((x === y) <=> phi(x, a), x, x)
      andThen(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), phi(y1, a), in(y1, B), phi(x, a)) |- in(x, B)) by LeftExists.withParameters(forall(x, (y === x) <=> phi(x, a)), y)
      andThen(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), phi(y1, a) /\ in(y1, B), phi(x, a)) |- in(x, B)) by Rewrite
      andThen(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), exists(y1, phi(y1, a) /\ in(y1, B)), phi(x, a)) |- in(x, B)) by LeftExists.withParameters(phi(y1, a) /\ in(y1, B), y1)
      andThen(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), True ==> exists(y, phi(y, a) /\ in(y, B)), phi(x, a)) |- in(x, B)) by Rewrite
      andThen(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), in(a, A) ==> exists(y, phi(y, a) /\ in(y, B)), phi(x, a), in(a, A)) |- in(x, B)) by LeftSubstIff(
        List((True, in(a, A))),
        LambdaFormulaFormula(Seq(h), h() ==> exists(y, phi(y, a) /\ in(y, B)))
      )
      andThen(Set(exists(y, forall(x, (y === x) <=> phi(x, a))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a), in(a, A)) |- in(x, B)) by LeftForall.withParameters(
        in(a, A) ==> exists(y, phi(y, a) /\ in(y, B)),
        a,
        a
      )
      andThen(Set(in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a), in(a, A)) |- in(x, B)) by LeftSubstIff(
        List((True, in(a, A))),
        LambdaFormulaFormula(Seq(h), h() ==> exists(y, forall(x, (y === x) <=> phi(x, a))))
      )
      andThen(Set(forall(a, in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a)))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a), in(a, A)) |- in(x, B)) by LeftForall
        .withParameters(in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a))), a, a)

      andThen(Set(forall(a, in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a)))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), phi(x, a) /\ in(a, A)) |- in(x, B)) by Rewrite
      andThen(
        Set(forall(a, in(a, A) ==> exists(y, forall(x, (y === x) <=> phi(x, a)))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), exists(a, phi(x, a) /\ in(a, A))) |- in(x, B)
      ) by LeftExists.withParameters(phi(x, a) /\ in(a, A), a)

      andThen(Set(forall(a, in(a, A) ==> existsOne(x, phi(x, a))), forall(a, in(a, A) ==> exists(y, phi(y, a) /\ in(y, B))), exists(a, phi(x, a) /\ in(a, A))) |- in(x, B)) by Rewrite
    }
    val G = forall(a, in(a, A) ==> exists(y, in(y, B) /\ (phi(y, a))))
    val F = forall(x, iff(in(x, B1), in(x, B) /\ exists(a, in(a, A) /\ (phi(x, a)))))
    val left = in(x, B1)
    val right = in(x, B) /\ exists(a, in(a, A) /\ (phi(x, a)))

    val s9 = have(Set(F, in(x, B), exists(a, in(a, A) /\ (phi(x, a)))) |- in(x, B1)) subproof {
      val p0 = have(F |- F) by Hypothesis
      andThen("") by InstantiateForall(x)
      andThen(F |- (left ==> right) /\ (right ==> left)) by Rewrite
      andThen(F |- (right ==> left)) by destructRightAnd((right ==> left), (left ==> right)) // F |- in(x, B) /\ exists(a, in(a, A) /\ (phi(x, a))) => in(x, B1)
      andThen(Set(F, in(x, B), exists(a, in(a, A) /\ (phi(x, a)))) |- in(x, B1)) by Rewrite
    }
    have((s8.bot.left ++ s9.bot.left.filterNot(isSame(_, in(x, B)))) |- in(x, B1)) by Cut.withParameters(in(x, B))(s8, s9)
    val s11 = andThen(Set(H1, G, F) |- exists(a, in(a, A) /\ (phi(x, a))) ==> in(x, B1)) by Rewrite // F |- ∃a. a ∈ A ∧ x = (a, b) => (x ∈ B1)   --- half

    val s12 = have(F |- (in(x, B1) ==> exists(a, in(a, A) /\ (phi(x, a))))) subproof {
      val p0 = have(F |- F) by Hypothesis
      andThen("") by InstantiateForall(x: Term)
      andThen(F |- (left ==> right) /\ (right ==> left)) by Rewrite
      andThen(F |- (left ==> right)) by destructRightAnd((left ==> right), (right ==> left))
      andThen(Set(F, in(x, B1)) |- exists(a, in(a, A) /\ (phi(x, a))) /\ in(x, B)) by Rewrite
      andThen(Set(F, in(x, B1)) |- exists(a, in(a, A) /\ (phi(x, a)))) by destructRightAnd(exists(a, in(a, A) /\ (phi(x, a))), in(x, B))
      andThen(F |- (in(x, B1) ==> exists(a, in(a, A) /\ (phi(x, a))))) by Rewrite
    }
    val s13 =
      have((H1, G, F) |- in(x, B1) <=> exists(a, in(a, A) /\ (phi(x, a)))) by RightIff
        .withParameters(in(x, B1), exists(a, in(a, A) /\ (phi(x, a))))(s11, s12) // have F |- (x ∈ B1) <=> ∃a. a ∈ A ∧ x = (a, b)
    val s14 = andThen((H1, G, F) |- forall(x, in(x, B1) <=> exists(a, in(a, A) /\ (phi(x, a))))) by RightForall.withParameters(in(x, B1) <=> exists(a, in(a, A) /\ (phi(x, a))), x)
    have(Set(H1, G, F) |- (X === B1) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))) subproof {
      val left = Set(H1, G, F, forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))))
      have(Set(H1, G, F, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))) |- in(x, X) <=> in(x, B1)) by RightSubstIff(
        List((in(x, X), exists(a, in(a, A) /\ (phi(x, a))))),
        LambdaFormulaFormula(Seq(h), h() <=> in(x, B1))
      )(s13)
      andThen(left |- in(x, X) <=> in(x, B1)) by LeftForall.withParameters(in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))), x, x)
      val t2 =
        andThen(left |- forall(x, in(x, X) <=> in(x, B1))) by RightForall.withParameters(in(x, X) <=> in(x, B1), x) // redGoal2  F, [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)] |- ∀z. (z ∈ X) <=> (z ∈ B1)

      val t3 = have(forall(z, in(z, X) <=> in(z, B1)) <=> (X === B1)) by InstFunSchema(Map(x -> LambdaTermTerm(Seq(), X), y -> LambdaTermTerm(Seq(), B1)))(ax"extensionalityAxiom")
      val t4 = have(left ++ t3.bot.right |- X === B1) by RightSubstIff(List((X === B1, forall(z, in(z, X) <=> in(z, B1)))), LambdaFormulaFormula(Seq(h), h()))(t2)
      have((left |- X === B1)) by Cut.withParameters(t3.bot.right.head)(t3, t4)
      val t6 = andThen(Set(H1, G, F) |- forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))) ==> (X === B1)) by Rewrite
      have(Set(H1, G, F, X === B1) |- forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))) by RightSubstEq(
        List((X: Term, B1: Term)),
        LambdaTermFormula(Seq(f), forall(x, in(x, f) <=> exists(a, in(a, A) /\ phi(x, a))))
      )(s14)
      val t8 = andThen(Set(H1, G, F) |- X === B1 ==> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))) by Rewrite
      have(Set(H1, G, F) |- (X === B1) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))) by RightIff.withParameters(
        X === B1,
        forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))
      )(t6, t8)
    }

    andThen((H1, G, F) |- forall(X, (X === B1) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))))) by RightForall.withParameters(
      (X === B1) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))),
      X
    )
    val s17 = andThen((H1, G, F) |- exists(y, forall(X, (X === y) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))))) by RightExists.withParameters(
      forall(X, (X === y) <=> forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a))))),
      y,
      B1
    )
    val s18 = andThen((exists(B1, F), G, H1) |- s17.bot.right) by LeftExists.withParameters(F, B1) //  ∃B1. F |- ∃B1. ∀X. X=B1 <=> [∀x. (x ∈ X) <=> ∃a. a ∈ A ∧ x = (a, b)]
    val s19 = andThen(s18.bot.left |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))))) by Rewrite
    val s20 = have(() |- exists(B1, F)) by InstFunSchema(Map(y -> LambdaTermTerm(Seq(), B1)))(s7)
    have((G, H1) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))))) by Cut.withParameters(exists(B1, F))(s20, s19)
    val s21 = andThen((H1, exists(B, G)) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ (phi(x, a)))))) by LeftExists.withParameters(G, B)
    have(H1 |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ phi(x, a))))) by Cut.withParameters(exists(B, G))(s6, s21)
    andThen("∀ 'a. elem('a, 'A) ⇒ (∃! 'x. 'phi('x, 'a)) ⊢ ∃! 'X. ∀ 'x. elem('x, 'X) ↔ (∃ 'a. elem('a, 'A) ∧ 'phi('x, 'a))") by Rewrite
  }
  show

  val lemmaLayeredTwoArgumentsMap = makeTHM(
    "∀ 'b. elem('b, 'B) ⇒ (∀ 'a. elem('a, 'A) ⇒ (∃! 'x. 'psi('x, 'a, 'b))) ⊢ ∃!'X. ∀ 'x. elem('x, 'X) ↔ (∃ 'b. elem('b, 'B) ∧ (∀ 'x1. elem('x1, 'x) ↔ (∃ 'a. elem('a, 'A) ∧ 'psi('x1, 'a, 'b))))"
  ) {
    val a = variable
    val b = variable
    val x1 = variable
    val f = variable
    val A = variable
    val X = variable
    val B = variable
    val B1 = variable
    val phi = predicate(2)
    val psi = predicate(3)
    val H = existsOne(x, phi(x, a))
    val H1 = forall(a, in(a, A) ==> H)
    val H2 = instantiatePredicateSchemas(H1, Map(phi -> LambdaTermFormula(Seq(x, a), psi(x, a, b))))

    have((H2) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b))))) by InstPredSchema(
      Map(phi -> LambdaTermFormula(Seq(x, a), psi(x, a, b)))
    )(thm"functionalMapping")

    andThen((H2, in(b, B)) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b))))) by Weakening
    andThen((in(b, B) ==> H2, in(b, B)) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b))))) by LeftSubstIff(List((in(b, B), And())), LambdaFormulaFormula(Seq(h), h() ==> H2))
    andThen((forall(b, in(b, B) ==> H2), in(b, B)) |- existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b))))) by LeftForall.withParameters(in(b, B) ==> H2, b, b)
    andThen(forall(b, in(b, B) ==> H2) |- in(b, B) ==> existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b))))) by Rewrite
    val s5 = andThen(forall(b, in(b, B) ==> H2) |- forall(b, in(b, B) ==> existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b)))))) by RightForall.withParameters(
      in(b, B) ==> existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b)))),
      b
    )

    have(forall(b, in(b, B) ==> existsOne(X, phi(X, b))) |- instantiateTermSchemas(thm"functionalMapping".proposition.right.head, Map(A -> LambdaTermTerm(Nil, B)))) by InstFunSchema(
      Map(A -> LambdaTermTerm(Nil, B))
    )(thm"functionalMapping")
    val s7 = andThen(
      forall(b, in(b, B) ==> existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b))))) |- existsOne(
        X,
        forall(x, in(x, X) <=> exists(b, in(b, B) /\ forall(x1, in(x1, x) <=> exists(a, in(a, A) /\ psi(x1, a, b)))))
      )
    ) by InstPredSchema(
      Map(phi -> LambdaTermFormula(Seq(y, b), forall(x, in(x, y) <=> exists(a, in(a, A) /\ psi(x, a, b)))))
    )

    val s8 = have(forall(b, in(b, B) ==> H2) |- existsOne(X, forall(x, in(x, X) <=> exists(b, in(b, B) /\ forall(x1, in(x1, x) <=> exists(a, in(a, A) /\ psi(x1, a, b))))))) by Cut.withParameters(
      forall(b, in(b, B) ==> existsOne(X, forall(x, in(x, X) <=> exists(a, in(a, A) /\ psi(x, a, b)))))
    )(s5, s7)

  }
  show
  /*
val applyFunctionToUniqueObject = makeTHM("∃! 'x. 'phi('x) ⊢ ∃! 'z. ∃ 'x. ('z = 'F('x)) ∧ 'phi('x)") {
  val x1 = variable
  val z1 = variable
  val F = function(1)
  val f = variable
  val phi = predicate(1)
  val g = formulaVariable

  val g2 = have(forall(x, phi(x) <=> (x === x1)) |- exists(x, phi(x) /\ (F(x) === z)) ==> (F(x1) === z)) subproof {
    have(F(x1) === z |- F(x1) === z) by Hypothesis
    andThen((x === x1, F(x) === z) |- F(x1) === z) by LeftSubstEq(List((x, x1)), LambdaTermFormula(Seq(f), F(f) === z))
    andThen(Set(phi(x) <=> (x === x1), phi(x), F(x) === z) |- F(x1) === z) by LeftSubstIff(List((x === x1, phi(x))), LambdaFormulaFormula(Seq(g), g))
    andThen(Set(forall(x, phi(x) <=> (x === x1)), phi(x), F(x) === z) |- F(x1) === z) by LeftForall.withParameters(phi(x) <=> (x === x1), x, x)
    andThen(Set(forall(x, phi(x) <=> (x === x1)), phi(x) /\ (F(x) === z)) |- F(x1) === z) by Rewrite
    andThen(Set(forall(x, phi(x) <=> (x === x1)), exists(x, phi(x) /\ (F(x) === z))) |- F(x1) === z) by LeftExists.withParameters(phi(x) /\ (F(x) === z), x)
    andThen(forall(x, phi(x) <=> (x === x1)) |- exists(x, phi(x) /\ (F(x) === z)) ==> (F(x1) === z)) by Rewrite
  }

  val g1 = have(forall(x, (x === x1) <=> phi(x)) |- z === F(x1) ==> exists(x, (z === F(x)) /\ phi(x))) subproof {
    have(phi(x1) |- phi(x1)) by Hypothesis
    val s1 = andThen(forall(x, (x === x1) <=> phi(x)) |- phi(x1)) by LeftForall.withParameters((x === x1) <=> phi(x), x, x1)
    val s2 = have(z === F(x1) |- z === F(x1)) by Hypothesis
    have((forall(x, (x === x1) <=> phi(x)), z === F(x1)) |- (z === F(x1)) /\ phi(x1)) by RightAnd.withParameters(z === F(x1), phi(x1))(s2, s1)
    andThen((forall(x, (x === x1) <=> phi(x)), z === F(x1)) |- exists(x, (z === F(x)) /\ phi(x))) by RightExists.withParameters((z === F(x)) /\ phi(x), x, x1)
    andThen(forall(x, (x === x1) <=> phi(x)) |- z === F(x1) ==> exists(x, (z === F(x)) /\ phi(x))) by Rewrite
  }

  have(forall(x, (x === x1) <=> phi(x)) |- (z === F(x1)) <=> exists(x, (z === F(x)) /\ phi(x))) by RightIff.withParameters(z === F(x1), exists(x, (z === F(x)) /\ phi(x)))(g1, g2)
  andThen(forall(x, (x === x1) <=> phi(x)) |- forall(z, (z === F(x1)) <=> exists(x, (z === F(x)) /\ phi(x)))) by RightForall.withParameters((z === F(x1)) <=> exists(x, (z === F(x)) /\ phi(x)), z)
  andThen(forall(x, (x === x1) <=> phi(x)) |- exists(z1, forall(z, (z === z1) <=> exists(x, (z === F(x)) /\ phi(x))))) by RightExists.withParameters(
    forall(z, (z === z1) <=> exists(x, (z === F(x)) /\ phi(x))), z1, F(x1))
  andThen(exists(x1, forall(x, (x === x1) <=> phi(x))) |- exists(z1, forall(z, (z === z1) <=> exists(x, (z === F(x)) /\ phi(x))))) by LeftExists.withParameters(forall(x, (x === x1) <=> phi(x)), x1)
  andThen(existsOne(x, phi(x)) |- existsOne(z, exists(x, (z === F(x)) /\ phi(x)))) by Rewrite

}
show

val mapTwoArguments = makeTHM("∀ 'b. elem('b, 'B) ⇒ (∀ 'a. elem('a, 'A) ⇒ (∃! 'x. 'psi('x, 'a, 'b))) ⊢ " +
    "∃!'z. ∃'x. 'z = union('x) ∧ (∀ 'x_2. elem('x_2, 'x) ↔ " +
    "(∃ 'b. elem('b, 'B) ∧ (∀ 'x1. elem('x1, 'x_2) ↔ (∃ 'a. elem('a, 'A) ∧ 'psi('x1, 'a, 'b)))))") {
  val x1 = variable
  val a = variable
  val b = variable
  val F = function(1)
  val A = variable
  val B = variable
  val phi = predicate(1)
  val psi = predicate(3)

  val i1 = thm"lemmaLayeredTwoArgumentsMap"
  val i2 = thm"applyFunctionToUniqueObject"
  val rPhi = forall(x, in(x, y) <=> exists(b, in(b, B) /\ forall(x1, in(x1, x) <=> exists(a, in(a, A) /\ psi(x1, a, b)))))
  val seq0 = instantiatePredicateSchemaInSequent(i2.proposition, Map(phi -> LambdaTermFormula(Seq(y), rPhi)))
  val s0 = have(seq0) by InstPredSchema(Map(phi -> LambdaTermFormula(Seq(y), rPhi)))(i2)

  val seq1 = instantiateFunctionSchemaInSequent(seq0, Map(F -> LambdaTermTerm(Seq(x), union(x))))
  val s1 = andThen(seq1) by InstFunSchema(Map(F -> LambdaTermTerm(Seq(x), union(x))))
  have(i1.proposition.left |- seq1.right) by Cut.withParameters(seq1.left.head)(i1, s1)
}
show */
}
