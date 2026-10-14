package lisa.maths.SetTheory.Types.ADTv2.height

import lisa.maths.Quantifiers.existsEpsilon
import lisa.maths.SetTheory.Base.Union.∪
import lisa.maths.SetTheory.Base._
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.Ordinals.Integer.{emptyInOmega, existsInOmega, unionInOmega}
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Functions.UnionRange.unionRangeMembership
import lisa.maths.SetTheory.Types.ADTv2.support.tactics.Cuts
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST._
import lisa.utils.prooflib.ProofTacticLib.Arity

final class HeightTerms[N <: Arity](
    base: HeightADT[N],
    constructorsTheory: HeightConstructors[N],
    constructors: Seq[HeightConstructorData],
    term: Expr[Ind],
    termSatisfiesDefinition: THM
) {

  protected inline final def app(f: Expr[Ind], x: Expr[Ind]): Expr[Ind] =
    lisa.maths.SetTheory.Functions.Predef.app(f)(x)

  private val subsetOfUnion = Lemma(x ⊆ y |- x ⊆ (y ∪ z)) {
    val yInUnion = have(y ⊆ (y ∪ z)) by Restate.from(Union.leftSubset of (x := y, y := z))
    have(thesis) by Cut(yInUnion, Subset.transitivity of (x := x, y := y, z := y ∪ z))
  }

  /** Running union of a finite sequence of sets (left-nested, seeded with `∅`). */
  private def unionList(elems: Seq[Expr[Ind]]): Expr[Ind] =
    elems.foldLeft[Expr[Ind]](∅)(_ ∪ _)

  /** Closure of `ω` under finite unions: if every element of `elems` is in `N`, so is
    * their union [[unionList]]. Produces `seqAnd(elems.map(_ ∈ N)) |- unionList(elems) ∈ N`.
    */
  private def unionListInOmega(elems: Seq[Expr[Ind]])(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact = {
    val seed = have(∅ ∈ N) by Restate.from(emptyInOmega)
    elems
      .foldLeft[(proof.Fact, Expr[Ind], Expr[Prop])]((seed, ∅, True)) { case ((thm, u, hyp), nh) =>
        val newU = u ∪ nh
        val newHyp = if hyp == (True: Expr[Prop]) then nh ∈ N else hyp /\ nh ∈ N
        val unionStep = have((u ∈ N, nh ∈ N) |- newU ∈ N) by
          Restate.from(unionInOmega of (a := u, b := nh))
        if hyp == (True: Expr[Prop]) then have(nh ∈ N |- newU ∈ N) by Cut(thm, unionStep)
        else have((hyp, nh ∈ N) |- newU ∈ N) by Cut(thm, unionStep)
        val newThm = thenHave(newHyp |- newU ∈ N) by Restate
        (newThm, newU, newHyp)
      }
      ._1
  }

  /** Every member of a finite sequence is a subset of its union [[unionList]].
    * Produces `|- subset(ni, unionList(elems))` (assuming `ni` occurs in `elems`).
    */
  private def memberSubsetOfUnionList(elems: Seq[Expr[Ind]], ni: Expr[Ind])(using
      proof: lisa.SetTheoryLibrary.Proof
  ): proof.Fact = {
    val seed = have(True |- True) by Restate
    elems
      .foldLeft[(proof.Fact, Expr[Ind], Expr[Ind])]((seed, ∅, ∅)) { case ((thmAcc, u, lastN), nj) =>
        val curHyp = thmAcc.statement.left.head
        val newU = u ∪ nj
        val newN = if nj == ni then nj else lastN

        val stepThm =
          if nj == ni then
            // We reach `ni`: `ni ⊆ u ∪ ni` (covers the first element, where `u == ∅`).
            have(curHyp |- newN ⊆ newU) by Restate.from(Union.rightSubset of (x := u, y := ni))
          else if newN == ∅ then
            // `ni` not seen yet (tracked subset is `∅`): `∅ ⊆ newU`.
            have(curHyp |- newN ⊆ newU) by Restate.from(Subset.leftEmpty of (x := newU))
          else
            // Extend the established `ni ⊆ u` by another union member.
            have(curHyp |- newN ⊆ newU) by Cut(thmAcc, subsetOfUnion of (x := newN, y := u, z := nj))

        (stepThm, newU, newN)
      }
      ._1
  }

  private def constructorVarsInDomain(
      c: HeightConstructorData,
      s: Expr[Ind]
  ): Expr[Prop] = wellTypedFormula(c.signature)(s)

  val termHasHeight = Lemma(
    base.isHeight(h) |- x ∈ term <=> ∃(n, n ∈ N /\ x ∈ app(h, n))
  ) {
    // `term` is characterised by: x ∈ term  iff  x ∈ ⋃range(h) for *every* height h.
    val termDef = forall(h, base.isHeight(h) ==> x ∈ ⋃(range(h)))
    val termDefinition = have(x ∈ term <=> termDef) by InstantiateForall(x)(termSatisfiesDefinition)

    // Two halves of the defining equivalence, obtained by rewriting a hypothesis with it.
    val termIsDef = have(x ∈ term |- termDef) by
      Substitute(termDefinition)(have(x ∈ term |- x ∈ term) by Hypothesis)
    val defIsTerm = have(termDef |- x ∈ term) by
      Substitute(termDefinition)(have(termDef |- termDef) by Hypothesis)

    // Forward: x ∈ term and isHeight(h) give x ∈ ⋃range(h) by instantiating the ∀.
    have(termDef |- termDef) by Hypothesis
    thenHave(termDef |- base.isHeight(h) ==> x ∈ ⋃(range(h))) by InstantiateForall(h)
    val defGivesUnion = thenHave((termDef, base.isHeight(h)) |- x ∈ ⋃(range(h))) by Restate
    have((x ∈ term, base.isHeight(h)) |- x ∈ ⋃(range(h))) by Cut(termIsDef, defGivesUnion)
    val forward = thenHave(base.isHeight(h) |- x ∈ term ==> x ∈ ⋃(range(h))) by Restate

    // Backward: any other height f equals h (heightUniqueness), so x ∈ ⋃range(h) gives the ∀.
    have((f === h, x ∈ ⋃(range(h))) |- x ∈ ⋃(range(f))) by Congruence
    have((base.isHeight(f), base.isHeight(h), x ∈ ⋃(range(h))) |- x ∈ ⋃(range(f))) by
      Cut(constructorsTheory.heightUniqueness, lastStep)
    thenHave((base.isHeight(h), x ∈ ⋃(range(h))) |- base.isHeight(f) ==> x ∈ ⋃(range(f))) by RightImplies
    thenHave((base.isHeight(h), x ∈ ⋃(range(h))) |- forall(f, base.isHeight(f) ==> x ∈ ⋃(range(f)))) by RightForall
    have((base.isHeight(h), x ∈ ⋃(range(h))) |- x ∈ term) by Cut(lastStep, defIsTerm)
    val backward = thenHave(base.isHeight(h) |- x ∈ ⋃(range(h)) ==> x ∈ term) by RightImplies

    val termUnionIff = have(base.isHeight(h) |- x ∈ term <=> x ∈ ⋃(range(h))) by RightIff(forward, backward)

    // Unfold isHeight(h) to extract function(h) and dom(h) === N.
    val hFunction = have(base.isHeight(h) |- function(h)) by Weakening(base.heightIsCore)
    val hDom = have(base.isHeight(h) |- dom(h) === N) by Weakening(base.heightIsCore)

    // Membership in ⋃range(h) unfolds to an existential over the domain of h.
    val unionMem =
      have(base.isHeight(h) |- x ∈ ⋃(range(h)) <=> ∃(n, n ∈ dom(h) /\ x ∈ app(h, n))) by
        Cut(hFunction, unionRangeMembership of (z := x))

    // Chain the two equivalences, then replace dom(h) with N.
    val termExistsDom =
      have(base.isHeight(h) |- x ∈ term <=> ∃(n, n ∈ dom(h) /\ x ∈ app(h, n))) by
        Substitute(unionMem)(termUnionIff)
    have(thesis) by Substitute(hDom)(termExistsDom)
  }

  /** Per-argument "stage characterisation": typing `v` at the limit `term` is equivalent to
    * typing it at *some* finite stage `app(h, n)`.
    *   - `SelfRef`: this is exactly [[termHasHeight]] (typing depends on the stage).
    *   - `TypeArg`: the typing `v ∈ t` is stage-independent, so the equivalence is just the
    *     non-emptiness of `ω`.
    *
    * Produces `isHeight(h) |- atTerm <=> ∃n. (n ∈ N ∧ body(app(h, n)))`, with
    * `atTerm = v ∈ ty.getOrElse(term)` and `body(s) = v ∈ ty.getOrElse(s)`.
    */
  private def argStageIff(v: Expr[Ind], ty: ConstructorArg)(using
      proof: lisa.SetTheoryLibrary.Proof
  ): proof.Fact =
    ty match
      case SelfRef => termHasHeight of (x := v)
      case TypeArg(_) =>
        val t = ty.getOrElse(term)
        val body = ∃(n, n ∈ N /\ v ∈ t)
        // Backward: any stage witness yields `v ∈ t` directly.
        have((n ∈ N /\ v ∈ t) |- v ∈ t) by Restate
        thenHave(body |- v ∈ t) by LeftExists
        val bwd = thenHave(body ==> v ∈ t) by Restate
        // Forward: `ω` is non-empty, so `v ∈ t` gives some stage witness.
        have((n ∈ N, v ∈ t) |- n ∈ N /\ v ∈ t) by Restate
        thenHave((n ∈ N, v ∈ t) |- body) by RightExists
        thenHave((∃(n, n ∈ N), v ∈ t) |- body) by LeftExists
        have(v ∈ t |- body) by Cut(existsInOmega, lastStep)
        val fwd = thenHave(v ∈ t ==> body) by Restate
        have(v ∈ t <=> body) by RightIff(fwd, bwd)
        thenHave(base.isHeight(h) |- v ∈ t <=> body) by Weakening

  val termsHaveHeight = constructors
    .map(c =>
      c -> Lemma(
        base.isHeight(h) |-
          (constructorVarsInDomain(c, term) <=>
            ∃(n, n ∈ N /\ constructorVarsInDomain(c, app(h, n))))
      ) {
        // Per-argument typing predicates, as functions of a stage index `k`:
        //   atTerm(v, ty) = v ∈ ty.getOrElse(term)     -- a conjunct of `constructorVarsInDomain(c, term)`
        //   body(v, ty)(k) = v ∈ ty.getOrElse(app(h, k)) -- the matching conjunct at stage `k`
        // Their conjunction over the signature is exactly `constructorVarsInDomain`.
        val args = c.signature
        def bodyOf(v: Expr[Ind], ty: ConstructorArg)(k: Expr[Ind]): Expr[Prop] =
          v ∈ ty.getOrElse(app(h, k))
        def atTermOf(v: Expr[Ind], ty: ConstructorArg): Expr[Prop] =
          v ∈ ty.getOrElse(term)

        // ── Backward: a single stage `n` types every argument, hence types them at `term`. ──
        val backward = have(
          base.isHeight(h) |- ∃(n, n ∈ N /\ constructorVarsInDomain(c, app(h, n))) ==> constructorVarsInDomain(c, term)
        ) subproof {
          val andSeq = for (v, ty) <- args yield
            val atTerm = atTermOf(v, ty)
            val exStage = ∃(n, n ∈ N /\ bodyOf(v, ty)(n))
            // The per-argument stage equivalence, used backwards: `∃ stage  ⊢  typed at term`.
            val toTerm = have((base.isHeight(h), exStage) |- atTerm) by
              Substitute(argStageIff(v, ty))(have((base.isHeight(h), exStage) |- exStage) by Restate)

            have((n ∈ N /\ bodyOf(v, ty)(n)) |- n ∈ N /\ bodyOf(v, ty)(n)) by Restate
            thenHave((n ∈ N /\ bodyOf(v, ty)(n)) |- exStage) by RightExists
            have((base.isHeight(h), n ∈ N /\ bodyOf(v, ty)(n)) |- atTerm) by Cut(lastStep, toTerm)
            thenHave((base.isHeight(h), n ∈ N /\ constructorVarsInDomain(c, app(h, n))) |- atTerm) by Weakening

          // Conjoin the per-argument facts (empty signature ⇒ `constructorVarsInDomain` is `True`).
          if andSeq.isEmpty then
            have((base.isHeight(h), n ∈ N /\ constructorVarsInDomain(c, app(h, n))) |- constructorVarsInDomain(c, term)) by Restate
          else
            have((base.isHeight(h), n ∈ N /\ constructorVarsInDomain(c, app(h, n))) |- constructorVarsInDomain(c, term)) by
              RightAnd(andSeq*)
          thenHave((base.isHeight(h), ∃(n, n ∈ N /\ constructorVarsInDomain(c, app(h, n)))) |- constructorVarsInDomain(c, term)) by
            LeftExists
        }

        // ── Forward: each argument has a witness stage; their union is a common stage. ──
        val forward = have(
          base.isHeight(h) |- constructorVarsInDomain(c, term) ==> ∃(n, n ∈ N /\ constructorVarsInDomain(c, app(h, n)))
        ) subproof {
          val ctx = constructorVarsInDomain(c, term)

          // For each argument: pick a witness stage `wh` with ε, and record `wh ∈ N` and the typing there.
          val witnesses = args.map { (v, ty) =>
            val exStage = ∃(n, n ∈ N /\ bodyOf(v, ty)(n))
            val existsStage = have((base.isHeight(h), ctx) |- exStage) by
              Substitute(argStageIff(v, ty))(have((base.isHeight(h), ctx) |- atTermOf(v, ty)) by Restate)

            val wh = ε(n, n ∈ N /\ bodyOf(v, ty)(n))
            val whProp = have(exStage |- wh ∈ N /\ bodyOf(v, ty)(wh)) by
              Restate.from(existsEpsilon of (x := n, P := λ(n, n ∈ N /\ bodyOf(v, ty)(n))))
            val whBoth = have((base.isHeight(h), ctx) |- wh ∈ N /\ bodyOf(v, ty)(wh)) by Cut(existsStage, whProp)
            val whInNat = have((base.isHeight(h), ctx) |- wh ∈ N) by Weakening(whBoth)
            val whBody = have((base.isHeight(h), ctx) |- bodyOf(v, ty)(wh)) by Weakening(whBoth)

            (v, ty, wh, whInNat, whBody)
          }

          val whsInNat = witnesses.map(_._3)
          val whBodies = witnesses.map(_._4)
          val max = unionList(whsInNat)

          // `max ∈ N` by closure of ω under finite unions.
          val maxInNatFromSeq = have(seqAnd(whsInNat.map(_ ∈ N)) |- max ∈ N) by
            Restate.from(unionListInOmega(whsInNat))
          val allInNat =
            if whsInNat.isEmpty then have((base.isHeight(h), ctx) |- seqAnd(whsInNat.map(_ ∈ N))) by Restate
            else have((base.isHeight(h), ctx) |- seqAnd(whsInNat.map(_ ∈ N))) by RightAnd(whBodies*)
          val maxInNat = have((base.isHeight(h), ctx) |- max ∈ N) by Cut(allInNat, maxInNatFromSeq)

          // Lift each argument's typing from its own stage `wh` up to the common stage `max`.
          val bodiesAtMax = witnesses.map { (v, ty, wh, whInNat, whBody) => ty match
            case SelfRef =>
              val whInMax = have(wh ⊆ max) by Restate.from(memberSubsetOfUnionList(whsInNat, wh))
              have((base.isHeight(h), constructorVarsInDomain(c, term)) |- v ∈ app(h, max)) by
                Cuts(constructorsTheory.heightMembershipMonotonic of (x := v, m := wh, n := max))(
                  maxInNat,
                  whInNat,
                  whInMax,
                  whBody
                )
            case TypeArg(_) => whBody
          }

          val bodyAtMax =
            if bodiesAtMax.isEmpty then have((base.isHeight(h), ctx) |- constructorVarsInDomain(c, app(h, max))) by Restate
            else have((base.isHeight(h), ctx) |- constructorVarsInDomain(c, app(h, max))) by RightAnd(bodiesAtMax*)

          have((base.isHeight(h), ctx) |- max ∈ N /\ constructorVarsInDomain(c, app(h, max))) by
            RightAnd(maxInNat, bodyAtMax)
          thenHave((base.isHeight(h), ctx) |- ∃(n, n ∈ N /\ constructorVarsInDomain(c, app(h, n)))) by RightExists
          thenHave(thesis) by Restate
        }

        have(thesis) by RightIff(forward, backward)
      }
    )
    .toMap

}
