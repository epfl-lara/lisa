package lisa.maths.SetTheory.Types.ADTv2.recursion.proofs

import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.altEqualityTransitivity
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Predef.*

/**
 * Function-independent witness extensionality — proved once, instantiated at
 * each call site via [[extensionality]].of(...).
 *
 * The lemma captures the invariant that two witness applications `wL` and `wR`
 * (typically W(G(n)) and W(G(Succ(n)))) agree on an ambient term `ambT`,
 * given that they agree on the corresponding case body (a consequence of the
 * induction hypothesis). The proof is a fixed five-step transitivity chain:
 *
 *   wL(ambT) = wL(inpT)   (congruence from ambT = inpT)
 *            = bodyL       (witnessAtLeft)
 *            = bodyR       (bodyEq, from IH)
 *            = wR(inpT)    (witnessAtRight, reversed)
 *            = wR(ambT)    (congruence from ambT = inpT)
 *
 * Callers supply the function-specific ingredients — body substitution,
 * witness case instantiation, body equality from the IH — and then
 * instantiate [[extensionality]] with `.of(wL := ..., wR := ..., ...)`.
 */
private[recursion] object WitnessCaseExtensionality {

  /** Left witness function W(f), as a set term. */
  private val wL    = variable[Ind]
  /** Right witness function W(g), as a set term. */
  private val wR    = variable[Ind]
  /** Ambient term `a` (element of the ADT at height n+1). */
  private val ambT  = variable[Ind]
  /** Pattern's canonical input term `c(x̄)`. */
  private val inpT  = variable[Ind]
  /** Case body with the left self-reference substituted. */
  private val bodyL = variable[Ind]
  /** Case body with the right self-reference substituted. */
  private val bodyR = variable[Ind]

  /**
   * Generic lemma, wrapped by [[extensionalityAt]]:
   * {{{
   *   WitnessCaseExtensionality.extensionalityAt(
   *     leftWitness = recWitness(G(n)),
   *     rightWitness = recWitness(G(Succ(n))),
   *     ambientTerm = a,
   *     inputTerm = pattern.freshInputTerm,
   *     leftBody = bodyLeft,
   *     rightBody = bodyRight
   *   )
   * }}}
   * The instantiated fact can then be combined with `aEqPattern`,
   * `witnessAtLeft`, `witnessAtRight`, and `bodyEq` via `Tautology.from`.
   */
  private val extensionality: THM = Lemma(
    (ambT === inpT) /\ (app(wL)(inpT) === bodyL) /\ (app(wR)(inpT) === bodyR) /\ (bodyL === bodyR) |-
      (app(wL)(ambT) === app(wR)(ambT))
  ) {
    assume((ambT === inpT) /\ (app(wL)(inpT) === bodyL) /\ (app(wR)(inpT) === bodyR) /\ (bodyL === bodyR))

    val h1 = have(ambT === inpT)           by Tautology
    val h2 = have(app(wL)(inpT) === bodyL) by Tautology
    val h3 = have(app(wR)(inpT) === bodyR) by Tautology
    val h4 = have(bodyL === bodyR)         by Tautology

    val step1 = have(app(wL)(ambT) === app(wL)(inpT)) by Congruence.from(h1)

    val step2 = have(app(wL)(ambT) === bodyL) by Tautology.from(
      altEqualityTransitivity of (x := app(wL)(ambT), y := app(wL)(inpT), z := bodyL),
      step1, h2
    )

    val step3 = have(bodyR === app(wR)(inpT)) by Congruence.from(h3)

    have(bodyL === app(wR)(inpT)) by Tautology.from(
      altEqualityTransitivity of (x := bodyL, y := bodyR, z := app(wR)(inpT)),
      h4, step3
    )

    val step4 = have(app(wL)(ambT) === app(wR)(inpT)) by Tautology.from(
      altEqualityTransitivity of (x := app(wL)(ambT), y := bodyL, z := app(wR)(inpT)),
      step2, lastStep
    )

    val step5 = have(app(wR)(inpT) === app(wR)(ambT)) by Congruence.from(h1)

    have(thesis) by Tautology.from(
      altEqualityTransitivity of (x := app(wL)(ambT), y := app(wR)(inpT), z := app(wR)(ambT)),
      step4, step5
    )
  }

  def extensionalityAt(
      leftWitness: Expr[Ind],
      rightWitness: Expr[Ind],
      ambientTerm: Expr[Ind],
      inputTerm: Expr[Ind],
      leftBody: Expr[Ind],
      rightBody: Expr[Ind]
  )(using proof: lisa.SetTheoryLibrary.Proof): proof.Fact =
    extensionality.of(
      wL := leftWitness,
      wR := rightWitness,
      ambT := ambientTerm,
      inpT := inputTerm,
      bodyL := leftBody,
      bodyR := rightBody
    )

  def pointwiseAgreementAt(using proof: lisa.SetTheoryLibrary.Proof)(
      leftWitness: Expr[Ind],
      rightWitness: Expr[Ind],
      ambientTerm: Expr[Ind],
      inputTerm: Expr[Ind],
      leftBody: Expr[Ind],
      rightBody: Expr[Ind],
      ambientEqInput: proof.Fact,
      leftAtInput: proof.Fact,
      rightAtInput: proof.Fact,
      bodyEquality: proof.Fact
  ): proof.Fact =
    // `wL(ambT) = wR(ambT)` is a pure congruence/transitivity chain over the four
    // supplied equalities:
    //   wL(ambT) = wL(inpT) = leftBody = rightBody = wR(inpT) = wR(ambT)
    // `Congruence` closes it via e-graph reasoning, polynomial in term size. The
    // previous `Tautology.from(extensionality, …)` instead decomposed the facts'
    // left context (which carries the deep nested-pattern `branchSelectionBody`)
    // propositionally, which blew up exponentially for depth-2 patterns.
    have(ambientEqInput.statement.left |- (app(leftWitness)(ambientTerm) === app(rightWitness)(ambientTerm))) by
      Congruence.from(ambientEqInput, leftAtInput, rightAtInput, bodyEquality)

  def initialize(): Unit = {
    val _ = extensionality
  }
}
