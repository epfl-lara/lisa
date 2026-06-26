package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.Base.Pair.given
import lisa.maths.SetTheory.Ordinals.Integer.omegaSuccessorInduction
import lisa.maths.SetTheory.Ordinals.Ordinal.S
import lisa.maths.SetTheory.SetTheory._
import lisa.utils.prooflib.QuantifiersIntro
import lisa.utils.debug.Time
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.PropositionalFacts._
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST._
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.ProofTacticLib.Arity

private[encoding] trait SyntacticADTInduction[N <: Arity] extends SyntacticADTTerm[N] {
  this: SyntacticADT[N] =>

  lazy val inductiveCase: Map[SyntacticConstructor, Expr[Prop]] = constructors
    .map(c =>
      c -> c.signature.foldRight[Expr[Prop]](P(c.term))((el, fc) =>
        val (v, ty) = el
        ty match
          case SelfRef => forall(v, in(v, term) ==> (P(v) ==> fc))
          case TypeArg(typeName) => forall(v, in(v, typeExprToTerm(typeName)) ==> fc)
      )
    )
    .toMap

  val induction = Time.measure("ADT induction")(
    Lemma(using name = s"${name}/induction")(
      constructors.foldRight[Expr[Prop]](forall(x, in(x, term) ==> P(x)))((c, f) => inductiveCase(c) ==> f)
    ) {
      // The per-constructor inductive hypotheses the caller must supply, bundled together.
      val preconditions: Expr[Prop] = seqAnd(constructors.map(inductiveCase))

      // `stage(k)` states that every element of the height-`k` approximation satisfies P.
      // We prove the goal by ordinary induction over `k ∈ N` on this predicate.
      def stage(k: Expr[Ind]): Expr[Prop] = forall(x, in(x, app(h, k)) ==> P(x))
      val stageN: Expr[Prop] = stage(n)

      // --- Base case: the height-0 approximation is empty, so `stage(∅)` holds vacuously. ---
      have(isHeight(h) |- in(x, app(h, ∅)) ==> P(x)) by Weakening(heightZero)
      val baseCase = thenHave(isHeight(h) |- stage(∅)) by RightForall

      // Reduce the goal to the successor step: given the base case, ordinary induction over N
      // leaves only `stage(n) ==> stage(S(n))` to prove.
      val successorReduction = have(
        (isHeight(h), forall(n, in(n, N) ==> (stageN ==> stage(S(n))))) |-
          forall(n, in(n, N) ==> stageN)
      ) by Tautology.from(baseCase, omegaSuccessorInduction of (P := lam(n, stageN)))

      // --- Successor step: `stage(n) ==> stage(S(n))`. ---
      val successorStep = have(
        (isHeight(h), preconditions) |- forall(n, in(n, N) ==> (stageN ==> stage(S(n))))
      ) subproof {
        // `in(n, N)` and `stage(n)` are carried explicitly (via `ctx`) since the closing
        // steps discharge them; only the permanent hypotheses are assumed.
        assume(isHeight(h), preconditions)

        // An element of the height-`S(n)` approximation is an instance `c(args)` of some
        // constructor whose arguments live in the height-`n` approximation. We show that any
        // such instance satisfies P.
        def ctx(extra: Expr[Prop]*): Seq[Expr[Prop]] =
          Seq(isHeight(h), preconditions, in(n, N), stageN) ++ extra

        val instanceSatisfiesP = have(ctx(isConstructor(x, app(h, n))) |- P(x)) subproof {
          if constructors.isEmpty then have(thesis) by Restate
          else
            val perConstructor = constructors.map { c =>
              val argsInStage = wellTypedFormula(c.signature2)(app(h, n))
              val argsInTerm = wellTypedFormula(c.signature2)(term)

              // (1) Arguments living in the height-`n` approximation also live in the whole ADT.
              val argsInTermFromStage = have((isHeight(h), in(n, N), argsInStage) |- argsInTerm) subproof {
                assume(isHeight(h), in(n, N), argsInStage)
                val conjuncts = c.signature2.map { (v, ty) =>
                  ty match
                    case SelfRef =>
                      val vHasHeight = (∃(n, in(n, N) /\ in(x, app(h, n)))).substitute(x := v)
                      have(in(n, N) /\ in(v, app(h, n))) by Restate
                      thenHave(vHasHeight) by RightExists
                      have(in(v, term)) by Tautology.from(termHasHeight of (x := v), lastStep)
                    case TypeArg(typeName) =>
                      have(in(v, typeExprToTerm(typeName))) by Restate
                }
                if conjuncts.isEmpty then have(thesis) by Restate
                else have(thesis) by RightAnd(conjuncts*)
              }

              // (2) Discharging the constructor's inductive hypothesis yields `P(c(args))`.
              //     The membership hypotheses are taken from (1); the `P` hypotheses from `stage(n)`.
              def cCtx(extra: Expr[Prop]*): Seq[Expr[Prop]] =
                Seq(isHeight(h), inductiveCase(c), in(n, N), stageN) ++ extra

              val pOnInstance = have(cCtx(argsInStage) |- P(c.term2)) subproof {
                assume(isHeight(h), inductiveCase(c), in(n, N), stageN, argsInStage)
                have(inductiveCase(c)) by Restate
                c.signature2.foldLeft(lastStep) { (fact, el) =>
                  val (v, ty) = el
                  fact.statement.right.head match
                    case forall(boundVar, body) =>
                      val instantiated = body.substitute(boundVar := v)
                      thenHave(instantiated) by InstantiateForall(v)
                      (instantiated, ty) match
                        case (implies(_, implies(_, conclusion)), SelfRef) =>
                          val dischargeMembership = thenHave((argsInTerm, P(v)) |- conclusion) by Weakening
                          have(stageN |- stageN) by Hypothesis
                          thenHave(stageN |- in(v, app(h, n)) ==> P(v)) by InstantiateForall(v)
                          thenHave((stageN, argsInStage) |- P(v)) by Weakening
                          have(argsInTerm |- conclusion) by Cut(lastStep, dischargeMembership)
                          have(conclusion) by Cut(argsInTermFromStage, lastStep)
                        case (implies(_, conclusion), TypeArg(_)) =>
                          thenHave(conclusion) by Restate
                        case _ => throw UnreachableException
                    case _ => throw UnreachableException
                }
                thenHave(thesis) by Restate
              }

              // (3) Rewrite `c(args)` to `x`, then repack the arguments into the existential.
              have(cCtx(argsInStage, x === c.term2) |- P(x)) by Congruence.from(pOnInstance)
              thenHave(cCtx(argsInStage /\ (x === c.term2)) |- P(x)) by LeftAnd
              thenHave(cCtx(isConstructor(c, x, app(h, n))) |- P(x)) by QuantifiersIntro(c.variables2)
              thenHave(ctx(isConstructor(c, x, app(h, n))) |- P(x)) by Weakening
            }

            have(ctx(isConstructor(x, app(h, n))) |- P(x)) by LeftOr(perConstructor*)
        }

        // The height-`S(n)` approximation is exactly the constructor instances over height `n`.
        have((isHeight(h), in(n, N), in(x, app(h, S(n)))) |- isConstructor(x, app(h, n))) by
          Cut(heightSuccessorStrong, equivalenceApply of (p1 := in(x, app(h, S(n))), p2 := isConstructor(x, app(h, n))))
        have(ctx(in(x, app(h, S(n)))) |- P(x)) by Cut(lastStep, instanceSatisfiesP)
        thenHave(ctx() |- in(x, app(h, S(n))) ==> P(x)) by RightImplies
        thenHave(ctx() |- stage(S(n))) by RightForall
        thenHave((isHeight(h), preconditions, in(n, N)) |- stageN ==> stage(S(n))) by RightImplies
        thenHave((isHeight(h), preconditions) |- in(n, N) ==> (stageN ==> stage(S(n)))) by RightImplies
        thenHave(thesis) by RightForall
      }

      // --- Conclusion: every element of `term` has some height `n`, hence satisfies P. ---
      have((isHeight(h), preconditions) |- forall(n, in(n, N) ==> stageN)) by
        Cut(successorStep, successorReduction)
      thenHave((isHeight(h), preconditions) |- in(n, N) ==> stageN) by InstantiateForall(n)
      thenHave((isHeight(h), preconditions, in(n, N)) |- stageN) by Restate
      thenHave((isHeight(h), preconditions, in(n, N)) |- in(x, app(h, n)) ==> P(x)) by InstantiateForall(x)
      thenHave((isHeight(h), preconditions, in(n, N) /\ in(x, app(h, n))) |- P(x)) by Restate
      val heightImpliesP = thenHave(
        (isHeight(h), preconditions, exists(n, in(n, N) /\ in(x, app(h, n)))) |- P(x)
      ) by LeftExists

      have((isHeight(h), in(x, term)) |- exists(n, in(n, N) /\ in(x, app(h, n)))) by
        Cut(termHasHeight, equivalenceApply of (p1 := in(x, term), p2 := exists(n, in(n, N) /\ in(x, app(h, n)))))
      have((isHeight(h), preconditions, in(x, term)) |- P(x)) by Cut(lastStep, heightImpliesP)
      thenHave((exists(h, isHeight(h)), preconditions, in(x, term)) |- P(x)) by LeftExists
      have((preconditions, in(x, term)) |- P(x)) by Cut(heightExists, lastStep)
      thenHave(preconditions |- in(x, term) ==> P(x)) by RightImplies
      thenHave(preconditions |- forall(x, in(x, term) ==> P(x))) by RightForall
      thenHave(thesis) by Restate
    }
  )
}
