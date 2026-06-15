package lisa.maths.SetTheory.Cardinal

import lisa.maths.Quantifiers._
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions.Predef._

import Cardinal._

object Universe extends lisa.Main:
  private val U, U1, G, I = variable[Ind]
  private val s, x, y, z = variable[Ind]
  private val P, Q, N = variable[Ind >>: Prop]

  /**
   * Definition --- Structual definition of the Tarski/Grothendieck Universe U.
   *
   * A set U is a Tarski Universe if it is a non-empty set that is closed
   * under the fundamental operations of ZFC set theory. The existence o
   * f such a
   * set (the Tarski Axiom) is equivalent to assuming the existence of a
   * Strongly Inaccessible Cardinal κ, where U is often Vκ.
   *
   * The universe U must satisfy:
   * 1. Non-empty: U =/= ∅.
   * 2. Transitivity: ∀y ∈ U. x ∈ y ==> x ∈ U
   * 3. Pairing Closure: ∀x, y ∈ U. (x, y) ∈ U
   * 4. Union Closure: ∀x ∈ U. ∪(x) ∈ U
   * 5. Power Set Closure: ∀x ∈ U. 𝒫(x) ∈ U
   *
   * `isUniverse(U) <=> U ≠ ∅ ∧ transitiveSet(U) ∧ ...`
   *
   * @see [[TransitiveSet]]
   * @see [[tarskiAxiom]]
   */
  val isUniverse = DEF(
    λ(
      U,
      // 1. Transitivity: ∀x ∈ U. x ⊆ U
      (∀(x, (x ∈ U) ==> (x ⊆ U))) /\
        // 2. Pairing: ∀x, y ∈ U. {x, y} ∈ U
        (∀(x, ∀(y, (x ∈ U /\ y ∈ U) ==> (unorderedPair(x, y) ∈ U)))) /\
        // 3. Power Set: ∀x ∈ U. P(x) ∈ U
        (∀(x, (x ∈ U) ==> (⋃(x) ∈ U))) /\
        // 4. Union: ∀x ∈ U. ∪x ∈ U
        (∀(x, (x ∈ U) ==> (𝒫(x) ∈ U))) /\
        // 5. Replacement closure
        (∀(A, (A ∈ U) ==> ∀(f, (functionBetween(f)(A)(U)) ==> (range(f) ∈ U))))
    )
  )

  /**
   * Definition of universeOf(x).
   * The smallest (or chosen) universe containing x.
   */
  val universeOf = DEF(λ(x, ε(U, (x ∈ U) /\ isUniverse(U))))

  /**
   * Lemma related to sugar for epsilon and replacement.
   */
  private def _pair(x: Expr[Ind], y: Expr[Ind]): Expr[Ind] = unorderedPair(unorderedPair(x, x), unorderedPair(x, y))
  val existsReplacement = Lemma(
    (∃(x, P(x) /\ Q(x)), ∀(y, Q(y) <=> N(y))) |- ∃(x, P(x) /\ N(x))
  ) {
    have(∀(x, Q(x) <=> N(x)) |- ∀(x, Q(x) <=> N(x))) by Hypothesis
    thenHave(∀(x, Q(x) <=> N(x)) |- Q(x) <=> N(x)) by InstantiateForall(x)
    thenHave((P(x) /\ Q(x), ∀(x, Q(x) <=> N(x))) |- (P(x) /\ N(x))) by Tautology.fromLastStep()
    thenHave((P(x) /\ Q(x), ∀(x, Q(x) <=> N(x))) |- ∃(x, P(x) /\ N(x))) by RightExists
    thenHave((P(x) /\ Q(x), ∀(y, Q(y) <=> N(y))) |- ∃(x, P(x) /\ N(x))) by Restate
    thenHave(thesis) by LeftExists
  }

  /**
   * Lemma --- Equivalence between the standard ordered pair and the raw axiomatic pair.
   *
   * The standard library defines `(a, b)` as `{{a}, {a, b}}`.
   * The Tarski Axiom uses a raw construction `_pair(a, b)` which expands to `{{a, a}, {a, b}}`.
   *
   * This theorem proves that since `{a} = {a, a}` (by definition of singleton),
   * the two representations are extensionally equal.
   *
   * `(a, b) === _pair(a, b)`
   */
  val rawPairEquivalence = Lemma((a, b) === _pair(a, b)) {
    have((a, b) === unorderedPair(singleton(a), unorderedPair(a, b))) by Congruence.from(Pair.pair.definition of (x := a, y := b))
    thenHave(thesis) by Substitute(singleton.definition of (x := a))
  }

  /**
   * Theorem --- The Axiom of Replacement implies that the range of a function defined on a set in U is also in U.
   *
   * This theorem acts as a bridge between the low-level, set-theoretic formulation of the Axiom of Replacement
   * (expressed in terms of functional graphs and raw pairs) and the high-level library abstraction of functions.
   *
   * It establishes that if the raw Axiom holds, then for any set `A ∈ U` and any function `functionBetween(f)(A)(U)`,
   * the range of `f` is a valid set within the universe `U`.
   *
   * `(Raw Axiom of Replacement) |- (A ∈ U) ==> (functionBetween(f)(A)(U)) ==> (range(f) ∈ U)`
   */
  val replacementImpliesFunctionRange = Theorem(
    (∀(
      A,
      (A ∈ U) ==> ∀(
        G,
        ∀(a, a ∈ A ==> ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ G) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ G)) ==> (z === b))))) ==>
          ∃(I, (I ∈ U) /\ ∀(b, b ∈ I <=> ∃(a, (a ∈ A) /\ (_pair(a, b) ∈ G))))
      )
    )) |- (∀(A, (A ∈ U) ==> ∀(f, (functionBetween(f)(A)(U)) ==> (range(f) ∈ U))))
  ) {
    assume(
      ∀(
        A,
        (A ∈ U) ==> ∀(
          G,
          ∀(a, a ∈ A ==> ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ G) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ G)) ==> (z === b))))) ==> ∃(I, (I ∈ U) /\ ∀(b, b ∈ I <=> ∃(a, (a ∈ A) /\ (_pair(a, b) ∈ G))))
        )
      )
    )
    val replacementSchema = thenHave(
      (A ∈ U) ==> ∀(
        G,
        ∀(a, a ∈ A ==> ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ G) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ G)) ==> (z === b))))) ==> ∃(I, (I ∈ U) /\ ∀(b, b ∈ I <=> ∃(a, (a ∈ A) /\ (_pair(a, b) ∈ G))))
      )
    ) by InstantiateForall(A)
    have(thesis) subproof {
      have((A ∈ U, functionBetween(f)(A)(U)) |- range(f) ∈ U) subproof {
        assume(A ∈ U)
        assume(functionBetween(f)(A)(U))
        have(functionBetween(f)(A)(U)) by Hypothesis
        val fDef = thenHave(relationBetween(f)(A)(U) /\ ∀(x ∈ A, ∃!(y, (x, y) ∈ f))) by Substitute(functionBetween.definition of (B := U))
        have(relationBetween(f)(A)(U)) by Tautology.from(fDef)
        val fRelation = thenHave(f ⊆ (A × U)) by Substitute(relationBetween.definition of (R := f, X := A, Y := U))
        val fUniq = have(∀(x ∈ A, ∃!(y, (x, y) ∈ f))) by Tautology.from(fDef)
        thenHave(a ∈ A ==> ∃!(y, (a, y) ∈ f)) by InstantiateForall(a)
        val existsStd = thenHave(a ∈ A ==> ∃(x, (a, x) ∈ f /\ ∀(y, (a, y) ∈ f ==> (y === x)))) by Substitute(∃!.definition of (P := λ(y, (a, y) ∈ f)))
        have(a ∈ A |- ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ f) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ f)) ==> (z === b))))) subproof {
          assume(a ∈ A)
          have(∃(x, (a, x) ∈ f /\ ∀(y, (a, y) ∈ f ==> (y === x)))) by Tautology.from(existsStd)
          have(
            (a, x) ∈ f /\ ∀(y, (a, y) ∈ f ==> (y === x)) |-
              ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ f) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ f)) ==> (z === b))))
          ) subproof {
            assume((a, x) ∈ f)
            assume(∀(y, (a, y) ∈ f ==> (y === x)))
            val pairInf = have((a, x) ∈ f) by Hypothesis
            val underpairInf = thenHave(_pair(a, x) ∈ f) by Substitute(rawPairEquivalence of (b := x))
            have(a ∈ A /\ x ∈ U) by Tautology.from(
              pairInf,
              fRelation,
              Subset.membership of (x := f, y := (A × U), z := (a, x)),
              CartesianProduct.pairMembership of (x := a, y := x, B := U)
            )
            val x_in_U = have(x ∈ U) by Weakening(lastStep)
            have(∀(y, (a, y) ∈ f ==> (y === x))) by Hypothesis
            val stdUniq = thenHave((a, z) ∈ f ==> (z === x)) by InstantiateForall(z)
            have((z ∈ U, (_pair(a, z) ∈ f)) |- (z === x)) subproof {
              assume(z ∈ U)
              assume(_pair(a, z) ∈ f)
              have(_pair(a, z) ∈ f) by Hypothesis
              thenHave((a, z) ∈ f) by Substitute(rawPairEquivalence of (b := z))
              have(z === x) by Tautology.from(lastStep, stdUniq)
            }
            thenHave((z ∈ U /\ (_pair(a, z) ∈ f)) ==> (z === x)) by Restate
            thenHave(∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ f)) ==> (z === x))) by RightForall
            thenHave((x ∈ U) /\ (_pair(a, x) ∈ f) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ f)) ==> (z === x)))) by Tautology.fromLastStep(x_in_U, underpairInf)
            thenHave(∃(x, (x ∈ U) /\ (_pair(a, x) ∈ f) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ f)) ==> (z === x))))) by RightExists
            thenHave(thesis) by Restate
          }
          thenHave(
            ∃(x, (a, x) ∈ f /\ ∀(y, (a, y) ∈ f ==> (y === x))) |-
              ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ f) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ f)) ==> (z === b))))
          ) by LeftExists
          thenHave(thesis) by Tautology.fromLastStep(existsStd)
        }
        thenHave(a ∈ A ==> ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ f) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ f)) ==> (z === b))))) by Restate
        val conditionFull = thenHave(
          ∀(a, a ∈ A ==> ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ f) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ f)) ==> (z === b)))))
        ) by RightForall
        have(A ∈ U) by Hypothesis
        thenHave(
          ∀(
            G,
            ∀(a, a ∈ A ==> ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ G) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ G)) ==> (z === b))))) ==> ∃(I, (I ∈ U) /\ ∀(b, b ∈ I <=> ∃(a, (a ∈ A) /\ (_pair(a, b) ∈ G))))
          )
        ) by Tautology.fromLastStep(replacementSchema)
        thenHave(
          ∀(a, a ∈ A ==> ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ f) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ f)) ==> (z === b))))) ==>
            ∃(I, (I ∈ U) /\ ∀(b, b ∈ I <=> ∃(a, (a ∈ A) /\ (_pair(a, b) ∈ f))))
        ) by InstantiateForall(f)
        val instance = thenHave(∃(I, (I ∈ U) /\ ∀(b, b ∈ I <=> ∃(a, (a ∈ A) /\ (_pair(a, b) ∈ f))))) by Tautology.fromLastStep(conditionFull)
        have((I ∈ U) /\ ∀(b, b ∈ I <=> ∃(a, (a ∈ A) /\ (_pair(a, b) ∈ f))) |- range(f) ∈ U) subproof {
          assume(I ∈ U)
          assume(∀(b, b ∈ I <=> ∃(a, (a ∈ A) /\ (_pair(a, b) ∈ f))))
          val exactSet = have(I === range(f)) subproof {
            val equivFormula = have(∃(a, (a ∈ A) /\ (_pair(a, y) ∈ f)) <=> ∃(a, (a ∈ A) /\ (a, y) ∈ f)) subproof {
              have(_pair(a, y) ∈ f <=> _pair(a, y) ∈ f) by Tautology
              thenHave(_pair(a, y) ∈ f <=> (a, y) ∈ f) by Substitute(rawPairEquivalence of (b := y))
              val forallFormula = thenHave(∀(a, _pair(a, y) ∈ f <=> (a, y) ∈ f)) by RightForall
              have(∃(a, (a ∈ A) /\ (_pair(a, y) ∈ f)) |- ∃(a, (a ∈ A) /\ (a, y) ∈ f)) by Tautology.from(
                forallFormula,
                existsReplacement of (P := λ(x, x ∈ A), Q := λ(x, _pair(x, y) ∈ f), N := λ(x, (x, y) ∈ f), x := a)
              )
              val `==>` = thenHave(∃(a, (a ∈ A) /\ (_pair(a, y) ∈ f)) ==> ∃(a, (a ∈ A) /\ (a, y) ∈ f)) by Restate
              have(∃(a, (a ∈ A) /\ ((a, y) ∈ f)) |- ∃(a, (a ∈ A) /\ (_pair(a, y) ∈ f))) by Tautology.from(
                forallFormula,
                existsReplacement of (P := λ(x, x ∈ A), N := λ(x, _pair(x, y) ∈ f), Q := λ(x, (x, y) ∈ f), x := a)
              )
              val `<==` = thenHave(∃(a, (a ∈ A) /\ ((a, y) ∈ f)) ==> ∃(a, (a ∈ A) /\ (_pair(a, y) ∈ f))) by Restate
              have(thesis) by Tautology.from(`==>`, `<==`)
            }
            val rangeLemma = have(∃(a, (a ∈ A) /\ (a, y) ∈ f) <=> y ∈ range(f)) subproof {
              have(y ∈ range(f) <=> y ∈ range(f)) by Tautology
              thenHave(y ∈ range(f) <=> y ∈ { snd(z) | z ∈ f }) by Substitute(range.definition of (R := f))
              val rangeExpanded = thenHave(y ∈ range(f) <=> ∃(z ∈ f, snd(z) === y)) by Tautology.fromLastStep(
                Replacement.membership of (F := λ(x, snd(x)), A := f, x := z)
              )
              have(∃(a, (a ∈ A) /\ (a, y) ∈ f) |- y ∈ range(f)) subproof {
                have((a ∈ A, (a, y) ∈ f) |- ∃(z ∈ f, snd(z) === y)) subproof {
                  assume(a ∈ A)
                  assume((a, y) ∈ f)
                  have(snd(a, y) === y) by Tautology.from(Pair.pairSnd of (x := a))
                  thenHave((a, y) ∈ f /\ (snd(a, y) === y)) by Tautology.fromLastStep()
                  thenHave(thesis) by RightExists
                }
                thenHave((a ∈ A /\ (a, y) ∈ f) |- ∃(z ∈ f, snd(z) === y)) by Restate
                thenHave(∃(a, (a ∈ A) /\ (a, y) ∈ f) |- ∃(z, z ∈ f /\ (snd(z) === y))) by LeftExists
                thenHave(∃(a, (a ∈ A) /\ (a, y) ∈ f) |- ∃(z ∈ f, snd(z) === y)) by Restate
                thenHave(thesis) by Tautology.fromLastStep(rangeExpanded)
              }
              val `==>` = thenHave(∃(a, (a ∈ A) /\ (a, y) ∈ f) ==> y ∈ range(f)) by Restate
              have(y ∈ range(f) |- ∃(a, (a ∈ A) /\ (a, y) ∈ f)) subproof {
                assume(y ∈ range(f))
                val cond = have(∃(z ∈ f, snd(z) === y)) by Tautology.from(rangeExpanded)
                have((z ∈ f /\ (snd(z) === y)) |- ∃(a, (a ∈ A) /\ (a, y) ∈ f)) subproof {
                  assume(z ∈ f /\ (snd(z) === y))
                  val sndIsY = have(snd(z) === y) by Tautology
                  val zInProduct = have(z ∈ (A × U)) by Tautology.from(fRelation, Subset.membership of (x := f, y := (A × U)))
                  val fstInA = thenHave(fst(z) ∈ A) by Tautology.fromLastStep(CartesianProduct.fstMembership of (B := U))
                  val zInversion = have(z === (fst(z), snd(z))) by Tautology.from(zInProduct, CartesianProduct.inversion of (B := U))
                  have(z ∈ f) by Tautology
                  thenHave((fst(z), snd(z)) ∈ f) by Substitute(zInversion)
                  thenHave((fst(z), y) ∈ f) by Substitute(sndIsY)
                  thenHave(fst(z) ∈ A /\ (fst(z), y) ∈ f) by Tautology.fromLastStep(fstInA)
                  thenHave(thesis) by RightExists
                }
                thenHave(∃(z ∈ f, snd(z) === y) |- ∃(a, (a ∈ A) /\ (a, y) ∈ f)) by LeftExists
                thenHave(thesis) by Tautology.fromLastStep(cond)
              }
              val `<==` = thenHave(y ∈ range(f) ==> ∃(a, (a ∈ A) /\ (a, y) ∈ f)) by Restate
              have(thesis) by Tautology.from(`==>`, `<==`)
            }
            have(∀(b, b ∈ I <=> ∃(a, (a ∈ A) /\ (_pair(a, b) ∈ f)))) by Hypothesis
            thenHave(y ∈ I <=> ∃(a, (a ∈ A) /\ (_pair(a, y) ∈ f))) by InstantiateForall(y)
            thenHave(y ∈ I <=> ∃(a, (a ∈ A) /\ (a, y) ∈ f)) by Tautology.fromLastStep(equivFormula)
            thenHave(y ∈ I <=> y ∈ range(f)) by Tautology.fromLastStep(rangeLemma)
            thenHave(thesis) by Extensionality
          }
          have(I ∈ U) by Hypothesis
          thenHave(range(f) ∈ U) by Substitute(exactSet)
        }
        thenHave(∃(I, (I ∈ U) /\ ∀(b, b ∈ I <=> ∃(a, (a ∈ A) /\ (_pair(a, b) ∈ f)))) |- range(f) ∈ U) by LeftExists
        thenHave(thesis) by Tautology.fromLastStep(instance)
      }
      thenHave(A ∈ U |- functionBetween(f)(A)(U) ==> range(f) ∈ U) by Restate
      thenHave(A ∈ U |- ∀(f, functionBetween(f)(A)(U) ==> range(f) ∈ U)) by RightForall
      thenHave(A ∈ U ==> ∀(f, functionBetween(f)(A)(U) ==> range(f) ∈ U)) by Restate
      thenHave(thesis) by RightForall
    }
  }

  /**
   * Theorem --- The Fundamental Existence Theorem of Tarski Universes.
   *
   * This theorem asserts the core postulate of Tarski-Grothendieck set theory:
   * For every set `x`, there exists a Universe `U` containing `x`.
   *
   * This proof bridges the gap between the raw [[tarskiAxiom]] (defined using low-level
   * primitives like `pair` and relational graphs) and the high-level [[isUniverse]]
   * predicate (defined using standard library concepts `range(f)`).
   *
   * It relies crucially on [[replacementImpliesFunctionRange]] to demonstrate that
   * the raw replacement property in the axiom implies the functional range closure
   * required by `isUniverse`.
   *
   * `∀x. ∃U. (x ∈ U) /\ isUniverse(U)`
   */
  val universeExistence = Theorem(
    ∀(x, ∃(U, (x ∈ U) /\ isUniverse(U)))
  ) {
    val xInU = x ∈ U
    val firstPart = (∀(x, (x ∈ U) ==> (x ⊆ U))) /\
      (∀(x, ∀(y, (x ∈ U /\ y ∈ U) ==> (unorderedPair(x, y) ∈ U)))) /\
      (∀(x, (x ∈ U) ==> (⋃(x) ∈ U))) /\
      (∀(x, (x ∈ U) ==> (𝒫(x) ∈ U)))
    val restPart = ∀(
      A,
      (A ∈ U) ==> ∀(
        G,
        ∀(a, a ∈ A ==> ∃(b, (b ∈ U) /\ (_pair(a, b) ∈ G) /\ (∀(z, ((z ∈ U) /\ (_pair(a, z) ∈ G)) ==> (z === b))))) ==>
          ∃(I, (I ∈ U) /\ ∀(b, b ∈ I <=> ∃(a, (a ∈ A) /\ (_pair(a, b) ∈ G))))
      )
    )
    val shiftPart = (∀(A, (A ∈ U) ==> ∀(f, (functionBetween(f)(A)(U)) ==> (range(f) ∈ U))))
    have(∀(x, ∃(U, xInU /\ firstPart /\ restPart))) by Tautology.from(tarskiAxiom)
    val instance = thenHave(∃(U, xInU /\ (firstPart /\ restPart))) by InstantiateForall(x)
    have(firstPart /\ restPart |- firstPart /\ shiftPart) by Tautology.from(replacementImpliesFunctionRange)
    thenHave(firstPart /\ restPart |- isUniverse(U)) by Substitute(isUniverse.definition)
    thenHave(xInU /\ (firstPart /\ restPart) |- xInU /\ isUniverse(U)) by Tautology.fromLastStep()
    thenHave(xInU /\ (firstPart /\ restPart) |- ∃(U, xInU /\ isUniverse(U))) by RightExists
    thenHave(∃(U, xInU /\ (firstPart /\ restPart)) |- ∃(U, xInU /\ isUniverse(U))) by LeftExists
    thenHave(∃(U, xInU /\ isUniverse(U))) by Tautology.fromLastStep(instance)
    thenHave(thesis) by RightForall
  }

  /**
   * Theorem --- universeOf(x) is a valid Universe containing x.
   *
   * Since we proved in [[universeExistence]] that for any `x`, there exists at least one
   * Universe `U` containing it, the epsilon operator (`universeOf(x)`) is guaranteed
   * to select a valid witness that satisfies both properties:
   * 1. It is a Universe.
   * 2. It contains `x`.
   */
  val universeOfIsUniverse = Theorem(
    isUniverse(universeOf(x)) /\ (x ∈ universeOf(x))
  ) {
    have(∀(x, ∃(U, (x ∈ U) /\ isUniverse(U)))) by Tautology.from(universeExistence)
    thenHave(∃(U, (x ∈ U) /\ isUniverse(U))) by InstantiateForall(x)
    thenHave(
      (x ∈ ε(U, (x ∈ U) /\ isUniverse(U))) /\ isUniverse(ε(U, (x ∈ U) /\ isUniverse(U)))
    ) by Tautology.fromLastStep(existsEpsilon of (x := U, P := λ(U, (x ∈ U) /\ isUniverse(U))))
    thenHave(x ∈ universeOf(x) /\ isUniverse(ε(U, (x ∈ U) /\ isUniverse(U)))) by Substitute(universeOf.definition)
    thenHave(x ∈ universeOf(x) /\ isUniverse(universeOf(x))) by Substitute(universeOf.definition)
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- Universe Transitivity Projection.
   * If U is a universe, then for any element x in U, x is a subset of U.
   */
  val universeTransitivity = Theorem(
    isUniverse(U) |- (x ∈ U) ==> (x ⊆ U)
  ) {
    have(isUniverse(U) |- ∀(x, (x ∈ U) ==> (x ⊆ U))) by Tautology.from(isUniverse.definition)
    thenHave(thesis) by InstantiateForall(x)
  }

  /**
   * Theorem --- Universe Pairing Closure Projection.
   * If x, y ∈ U, then {x, y} ∈ U.
   */
  val universePairingClosure = Theorem(
    isUniverse(U) |- (x ∈ U /\ y ∈ U) ==> (unorderedPair(x, y) ∈ U)
  ) {
    have(isUniverse(U) |- ∀(x, ∀(y, (x ∈ U /\ y ∈ U) ==> (unorderedPair(x, y) ∈ U)))) by Tautology.from(isUniverse.definition)
    thenHave(thesis) by InstantiateForall(x, y)
  }

  /**
   * Theorem --- Universe Union Closure Projection.
   * If x ∈ U, then ⋃x ∈ U.
   */
  val universeUnionClosure = Theorem(
    isUniverse(U) |- (x ∈ U) ==> (⋃(x) ∈ U)
  ) {
    have(isUniverse(U) |- ∀(x, (x ∈ U) ==> (⋃(x) ∈ U))) by Tautology.from(isUniverse.definition)
    thenHave(thesis) by InstantiateForall(x)
  }

  /**
   * Theorem --- Universe Power Set Closure Projection.
   * If x ∈ U, then P(x) ∈ U.
   */
  val universePowerSetClosure = Theorem(
    isUniverse(U) |- (x ∈ U) ==> (𝒫(x) ∈ U)
  ) {
    have(isUniverse(U) |- ∀(x, (x ∈ U) ==> (𝒫(x) ∈ U))) by Tautology.from(isUniverse.definition)
    thenHave(thesis) by InstantiateForall(x)
  }

  /**
   * Theorem --- Universe Replacement Closure Projection.
   * If A ∈ U and f: A -> U, then range(f) ∈ U.
   */
  val universeReplacementClosure = Theorem(
    isUniverse(U) |- (A ∈ U) ==> ((functionBetween(f)(A)(U)) ==> (range(f) ∈ U))
  ) {
    have(isUniverse(U) |- ∀(A, (A ∈ U) ==> ∀(f, (functionBetween(f)(A)(U)) ==> (range(f) ∈ U)))) by Tautology.from(isUniverse.definition)
    thenHave(isUniverse(U) |- (A ∈ U) ==> ∀(f, (functionBetween(f)(A)(U)) ==> (range(f) ∈ U))) by InstantiateForall(A)
    thenHave((isUniverse(U), (A ∈ U)) |- ∀(f, (functionBetween(f)(A)(U)) ==> (range(f) ∈ U))) by Restate
    thenHave((isUniverse(U), (A ∈ U)) |- (functionBetween(f)(A)(U)) ==> (range(f) ∈ U)) by InstantiateForall(f)
    thenHave(thesis) by Restate
  }

  /**
   * Theorem --- Product Closure in Universe.
   *
   * If A ∈ U and B ∈ U, then A × B ∈ U.
   */
  val universeProductClosure = Theorem(
    (isUniverse(U), A ∈ U, B ∈ U) |- (A × B) ∈ U
  ) {
    assumeAll
    have(unorderedPair(A, B) ∈ U) by Tautology.from(universePairingClosure of (x := A, y := B))
    thenHave(⋃(unorderedPair(A, B)) ∈ U) by Tautology.fromLastStep(universeUnionClosure of (x := unorderedPair(A, B)))
    thenHave((A ∪ B) ∈ U) by Substitute(Union.∪.definition of (x := A, y := B))
    thenHave(𝒫(A ∪ B) ∈ U) by Tautology.fromLastStep(universePowerSetClosure of (x := A ∪ B))
    thenHave(𝒫(𝒫(A ∪ B)) ∈ U) by Tautology.fromLastStep(universePowerSetClosure of (x := 𝒫(A ∪ B)))
    thenHave(𝒫(𝒫(𝒫(A ∪ B))) ∈ U) by Tautology.fromLastStep(universePowerSetClosure of (x := 𝒫(𝒫(A ∪ B))))
    val tricePowerInU = thenHave(𝒫(𝒫(𝒫(A ∪ B))) ⊆ U) by Tautology.fromLastStep(universeTransitivity of (x := 𝒫(𝒫(𝒫(A ∪ B)))))
    have((A × B) ⊆ 𝒫(𝒫(A ∪ B))) subproof {
      have(z ∈ (A × B) ==> z ∈ 𝒫(𝒫(A ∪ B))) subproof {
        assume(z ∈ (A × B))
        val fstInA = have(fst(z) ∈ A) by Tautology.from(CartesianProduct.fstMembership)
        val sndInB = have(snd(z) ∈ B) by Tautology.from(CartesianProduct.sndMembership)
        val zFormula = have(z === (fst(z), snd(z))) by Tautology.from(CartesianProduct.inversion)
        val fstInUnion = have(fst(z) ∈ (A ∪ B)) by Tautology.from(fstInA, Union.membership of (x := A, z := fst(z), y := B))
        val sndInUnion = have(snd(z) ∈ (A ∪ B)) by Tautology.from(sndInB, Union.membership of (x := A, z := snd(z), y := B))
        val pairInPS = have(unorderedPair(fst(z), snd(z)) ∈ 𝒫(A ∪ B)) by Tautology.from(
          PowerSet.unorderedPairMembership of (x := fst(z), y := snd(z), z := A ∪ B),
          fstInUnion,
          sndInUnion
        )
        have(unorderedPair(fst(z), fst(z)) ∈ 𝒫(A ∪ B)) by Tautology.from(
          fstInUnion,
          PowerSet.unorderedPairMembership of (x := fst(z), y := fst(z), z := A ∪ B)
        )
        val singletonInPS = thenHave(singleton(fst(z)) ∈ 𝒫(A ∪ B)) by Substitute(singleton.definition of (x := fst(z)))
        have(unorderedPair(singleton(fst(z)), unorderedPair(fst(z), snd(z))) ∈ 𝒫(𝒫(A ∪ B))) by Tautology.from(
          pairInPS,
          singletonInPS,
          PowerSet.unorderedPairMembership of (x := singleton(fst(z)), y := unorderedPair(fst(z), snd(z)), z := 𝒫(A ∪ B))
        )
        thenHave((fst(z), snd(z)) ∈ 𝒫(𝒫(A ∪ B))) by Substitute(pair.definition of (x := fst(z), y := snd(z)))
        thenHave(z ∈ 𝒫(𝒫(A ∪ B))) by Substitute(zFormula)
      }
      thenHave(∀(z, z ∈ (A × B) ==> z ∈ 𝒫(𝒫(A ∪ B)))) by RightForall
      thenHave(thesis) by Tautology.fromLastStep(subsetAxiom of (x := A × B, y := 𝒫(𝒫(A ∪ B))))
    }
    thenHave((A × B) ∈ 𝒫(𝒫(𝒫(A ∪ B)))) by Tautology.fromLastStep(PowerSet.membership of (x := A × B, y := 𝒫(𝒫(A ∪ B))))
    thenHave(thesis) by Tautology.fromLastStep(tricePowerInU, Subset.membership of (x := 𝒫(𝒫(𝒫(A ∪ B))), y := U, z := (A × B)))
  }

  /**
   * Theorem --- Universe Subset Closure.
   *
   * If A ∈ U and B ⊆ A, then B ∈ U.
   */
  val universeSubsetClosure = Theorem(
    (isUniverse(U), A ∈ U, B ⊆ A) |- B ∈ U
  ) {
    assumeAll
    have(𝒫(A) ∈ U) by Tautology.from(universePowerSetClosure of (x := A))
    val cond = have(𝒫(A) ⊆ U) by Tautology.from(universeTransitivity of (x := 𝒫(A)), lastStep)
    have(B ∈ 𝒫(A)) by Tautology.from(PowerSet.membership of (x := B, y := A))
    thenHave(thesis) by Tautology.fromLastStep(cond, Subset.membership of (x := 𝒫(A), y := U, z := B))
  }
