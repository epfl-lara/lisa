package lisa.maths.SetTheory.Functions
package Operations

import lisa.maths.Quantifiers
import lisa.maths.Quantifiers.∃!
import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Relations
import lisa.maths.SetTheory.Relations.Predef._

import Function.{functionBetween, functionOn, function, app, injective, surjective, bijective, abs}
import BasicTheorems.{appDefinition, inversion => _, _}
import Restriction._

/**
 * If `f` and `g` are two functions that agree on the intersection of their
 * domains, then `f ∪ g` is a function on the union of their domains.
 *
 * Note that in general, the union of two functions is not a function, as they
 * may disagree on the intersection of their domains.
 */
object Union extends lisa.Main {

  private val 𝓕 = variable[Ind]
  private val u, h, t, s = variable[Ind]
  private val w = variable[Ind]

  extension (f: Expr[Ind]) {
    private def apply(x: Expr[Ind]): Expr[Ind] = app(f)(x)
  }

  /**
   * Theorem --- The union of a set of functions that agree on the intersection
   * of their domains is a function.
   *
   * Proof in English:
   * We show ⋃(𝓕) is a function by proving functionBetween(⋃(𝓕))(dom(⋃(𝓕)))(range(⋃(𝓕))).
   * 1. Each f ∈ 𝓕 is a relation (since it is a function, hence a subset of some A×B).
   *    Therefore ⋃(𝓕) is a relation: for any z ∈ ⋃(𝓕), ∃f ∈ 𝓕 with z ∈ f;
   *    since f is a relation, z = (fst(z), snd(z)); thus fst(z) ∈ dom(⋃(𝓕)) and snd(z) ∈ range(⋃(𝓕)).
   * 2. Uniqueness: if (x,y) ∈ ⋃(𝓕) and (x,z) ∈ ⋃(𝓕), pick f,g ∈ 𝓕 with (x,y)∈f and (x,z)∈g.
   *    Then f(x)=y and g(x)=z (function application), and x ∈ dom(f)∩dom(g),
   *    so f(x)=g(x) by hypothesis, hence y=z.
   * 3. Existence: x ∈ dom(⋃(𝓕)) means ∃z∈⋃(𝓕). fst(z)=x. Since ⋃(𝓕) is a relation,
   *    z=(x,snd(z)), so (x,snd(z)) ∈ ⋃(𝓕).
   */
  val isFunction = Theorem(
    (
      ∀(f ∈ 𝓕, function(f)),
      ∀(f ∈ 𝓕, ∀(g ∈ 𝓕, ∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x))))
    ) |- function(⋃(𝓕))
  ) {
    assume(∀(f ∈ 𝓕, function(f)))
    assume(∀(f ∈ 𝓕, ∀(g ∈ 𝓕, ∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x)))))

    // 1. function(f) |- relation(f)
    val funcIsRel = have(function(f) |- relation(f)) subproof {
      have(functionBetween(f)(A)(B) |- relation(f)) by Tautology.from(
        functionBetween.definition,
        Relations.BasicTheorems.relationBetweenIsRelation of (R := f, X := A, Y := B)
      )
      thenHave(∃(B, functionBetween(f)(A)(B)) |- relation(f)) by LeftExists
      thenHave(∃(A, ∃(B, functionBetween(f)(A)(B))) |- relation(f)) by LeftExists
      thenHave(thesis) by Substitute(function.definition)
    }

    // 2. ⋃(𝓕) is a relation: for z ∈ ⋃(𝓕), ∃f ∈ 𝓕 with z ∈ f; f is a relation, so z=(fst(z),snd(z))
    val unionIsRel = have(relation(⋃(𝓕))) subproof {
      have((z ∈ f, f ∈ 𝓕) |- z === (fst(z), snd(z))) subproof {
        assume(z ∈ f); assume(f ∈ 𝓕)
        have(function(f)) subproof {
          have(∀(f ∈ 𝓕, function(f))) by Hypothesis
          thenHave(f ∈ 𝓕 ==> function(f)) by InstantiateForall(f)
          thenHave(thesis) by Tautology.fromLastStep()
        }
        thenHave(relation(f)) by Tautology.fromLastStep(funcIsRel)
        thenHave(thesis) by Tautology.fromLastStep(
          Relations.BasicTheorems.inversion of (R := f)
        )
      }
      val zFPair = lastStep
      val fstSndInUnion = have(z ∈ ⋃(𝓕) |- (fst(z), snd(z)) ∈ ⋃(𝓕)) subproof {
        assume(z ∈ ⋃(𝓕))
        have(∃(t, t ∈ 𝓕 /\ z ∈ t)) by Tautology.from(unionAxiom of (x := 𝓕))
        have((t ∈ 𝓕, z ∈ t) |- z === (fst(z), snd(z))) by Tautology.from(zFPair of (f := t))
        val tPairZ = lastStep
        have((t ∈ 𝓕, z ∈ t) |- (fst(z), snd(z)) ∈ ⋃(𝓕)) subproof {
          assume(t ∈ 𝓕); assume(z ∈ t)
          have(z === (fst(z), snd(z))) by Tautology.from(tPairZ)
          val pairInT = thenHave((fst(z), snd(z)) ∈ t) by Congruence
          have(t ∈ 𝓕 /\ (fst(z), snd(z)) ∈ t) by Tautology.from(pairInT)
          thenHave(∃(s, s ∈ 𝓕 /\ (fst(z), snd(z)) ∈ s)) by RightExists
          thenHave(thesis) by Tautology.fromLastStep(unionAxiom of (x := 𝓕, z := (fst(z), snd(z))))
        }
        thenHave((t ∈ 𝓕 /\ z ∈ t) |- (fst(z), snd(z)) ∈ ⋃(𝓕)) by Restate
        thenHave(∃(t, t ∈ 𝓕 /\ z ∈ t) |- (fst(z), snd(z)) ∈ ⋃(𝓕)) by LeftExists
        thenHave(thesis) by Tautology.fromLastStep(unionAxiom of (x := 𝓕))
      }
      have(z ∈ ⋃(𝓕) |- z ∈ (dom(⋃(𝓕)) × range(⋃(𝓕)))) subproof {
        assume(z ∈ ⋃(𝓕))
        // z ∈ ⋃(𝓕) → (fst(z), snd(z)) ∈ ⋃(𝓕)
        have((fst(z), snd(z)) ∈ ⋃(𝓕)) by Tautology.from(fstSndInUnion)
        // fst(z) ∈ dom(⋃(𝓕)) and snd(z) ∈ range(⋃(𝓕))
        val fstInDom = have(fst(z) ∈ dom(⋃(𝓕))) by Tautology.from(
          Relations.BasicTheorems.domainMembership of (R := ⋃(𝓕), x := fst(z), y := snd(z)),
          lastStep
        )
        val sndInRange = have(snd(z) ∈ range(⋃(𝓕))) by Tautology.from(
          Relations.BasicTheorems.rangeMembership of (R := ⋃(𝓕), x := fst(z), y := snd(z)),
          { have((fst(z), snd(z)) ∈ ⋃(𝓕)) by Tautology.from(fstSndInUnion); lastStep }
        )
        // z = (fst(z), snd(z)) from the pair form using zFPair with any t ∈ 𝓕 containing z
        have((t ∈ 𝓕, z ∈ t) |- z === (fst(z), snd(z))) by Tautology.from(zFPair of (f := t))
        thenHave((t ∈ 𝓕 /\ z ∈ t) |- z === (fst(z), snd(z))) by Restate
        thenHave(∃(t, t ∈ 𝓕 /\ z ∈ t) |- z === (fst(z), snd(z))) by LeftExists
        val zEqPair = thenHave(z === (fst(z), snd(z))) by Tautology.fromLastStep(
          unionAxiom of (x := 𝓕)
        )
        // (fst(z), snd(z)) ∈ dom × range
        val pairInProd = have((fst(z), snd(z)) ∈ (dom(⋃(𝓕)) × range(⋃(𝓕)))) by Tautology.from(
          CartesianProduct.pairMembership of (x := fst(z), y := snd(z), A := dom(⋃(𝓕)), B := range(⋃(𝓕))),
          fstInDom,
          sndInRange
        )
        // z = (fst(z), snd(z)) ∈ dom × range  →  z ∈ dom × range
        have(thesis) by Congruence.from(zEqPair, pairInProd)
      }
      thenHave(z ∈ ⋃(𝓕) ==> z ∈ (dom(⋃(𝓕)) × range(⋃(𝓕)))) by Restate
      thenHave(∀(z, z ∈ ⋃(𝓕) ==> z ∈ (dom(⋃(𝓕)) × range(⋃(𝓕))))) by RightForall
      thenHave(⋃(𝓕) ⊆ (dom(⋃(𝓕)) × range(⋃(𝓕)))) by Substitute(⊆.definition of (x := ⋃(𝓕), y := (dom(⋃(𝓕)) × range(⋃(𝓕)))))
      thenHave(∃(Y, ⋃(𝓕) ⊆ (dom(⋃(𝓕)) × Y))) by RightExists
      thenHave(∃(X, ∃(Y, ⋃(𝓕) ⊆ (X × Y)))) by RightExists
      thenHave(thesis) by Substitute(relation.definition of (R := ⋃(𝓕)))
    }

    // 3. ⋃(𝓕) ⊆ dom(⋃(𝓕)) × range(⋃(𝓕))
    val isRelBetween = have(relationBetween(⋃(𝓕))(dom(⋃(𝓕)))(range(⋃(𝓕)))) by Tautology.from(
      unionIsRel,
      Relations.BasicTheorems.relationBetweenDomainRange of (R := ⋃(𝓕))
    )

    // 4. Core uniqueness: if (x,y) ∈ ⋃(𝓕) and (x,z) ∈ ⋃(𝓕), then y = z
    val uniqueCore = have((f ∈ 𝓕, (x, y) ∈ f, g ∈ 𝓕, (x, z) ∈ g) |- (y === z)) subproof {
      assume(f ∈ 𝓕); assume((x, y) ∈ f); assume(g ∈ 𝓕); assume((x, z) ∈ g)

      val funF = have(function(f)) subproof {
        have(∀(f ∈ 𝓕, function(f))) by Hypothesis
        thenHave(f ∈ 𝓕 ==> function(f)) by InstantiateForall(f)
        thenHave(thesis) by Tautology.fromLastStep()
      }
      val funG = have(function(g)) subproof {
        have(∀(f ∈ 𝓕, function(f))) by Hypothesis
        thenHave(g ∈ 𝓕 ==> function(g)) by InstantiateForall(g)
        thenHave(thesis) by Tautology.fromLastStep()
      }
      val xInDomF = have(x ∈ dom(f)) by Tautology.from(
        Relations.BasicTheorems.domainMembership of (R := f, x := x, y := y)
      )
      val xInDomG = have(x ∈ dom(g)) by Tautology.from(
        Relations.BasicTheorems.domainMembership of (R := g, x := x, y := z)
      )
      val fxIsY = have(f(x) === y) by Tautology.from(
        appDefinition of (y := y),
        funF,
        xInDomF
      )
      val gxIsZ = have(g(x) === z) by Tautology.from(
        appDefinition of (f := g, y := z),
        funG,
        xInDomG
      )
      val xInInter = have(x ∈ (dom(f) ∩ dom(g))) by Tautology.from(
        Intersection.membership of (z := x, x := dom(f), y := dom(g)),
        xInDomF,
        xInDomG
      )
      val fxEqGx = have(f(x) === g(x)) subproof {
        // Instantiate the agree-on-intersection hypothesis for f, g, x
        have(∀(f ∈ 𝓕, ∀(g ∈ 𝓕, ∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x))))) by Hypothesis
        val step1 = thenHave(f ∈ 𝓕 ==> ∀(g ∈ 𝓕, ∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x)))) by InstantiateForall(f)
        val step2 = have(∀(g ∈ 𝓕, ∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x)))) by Tautology.from(step1)
        val step3 = thenHave(g ∈ 𝓕 ==> ∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x))) by InstantiateForall(g)
        val step4 = have(∀(x ∈ (dom(f) ∩ dom(g)), f(x) === g(x))) by Tautology.from(step3)
        val step5 = thenHave(x ∈ (dom(f) ∩ dom(g)) ==> (f(x) === g(x))) by InstantiateForall(x)
        have(thesis) by Tautology.from(step5, xInInter)
      }
      // y === f(x) === g(x) === z, so y === z
      have(y === f(x)) by Congruence.from(fxIsY)
      have(y === g(x)) by Congruence.from(lastStep, fxEqGx)
      have(thesis) by Congruence.from(lastStep, gxIsZ)
    }

    // Lift uniqueness to ⋃(𝓕)
    thenHave((f ∈ 𝓕 /\ (x, y) ∈ f, g ∈ 𝓕, (x, z) ∈ g) |- (y === z)) by Restate
    thenHave((∃(f, f ∈ 𝓕 /\ (x, y) ∈ f), g ∈ 𝓕, (x, z) ∈ g) |- (y === z)) by LeftExists
    thenHave((∃(f, f ∈ 𝓕 /\ (x, y) ∈ f), g ∈ 𝓕 /\ (x, z) ∈ g) |- (y === z)) by Restate
    thenHave((∃(f, f ∈ 𝓕 /\ (x, y) ∈ f), ∃(g, g ∈ 𝓕 /\ (x, z) ∈ g)) |- (y === z)) by LeftExists
    val unique = thenHave(((x, y) ∈ ⋃(𝓕), (x, z) ∈ ⋃(𝓕)) |- (y === z)) by Tautology.fromLastStep(
      unionAxiom of (x := 𝓕, z := (x, y)),
      unionAxiom of (x := 𝓕, z := (x, z))
    )

    // 5. Existence: x ∈ dom(⋃(𝓕)) → ∃y. (x,y) ∈ ⋃(𝓕)
    val existsY = have(x ∈ dom(⋃(𝓕)) |- ∃(y, (x, y) ∈ ⋃(𝓕))) subproof {
      assume(x ∈ dom(⋃(𝓕)))
      have(x ∈ { fst(z) | z ∈ ⋃(𝓕) } <=> ∃(z ∈ ⋃(𝓕), fst(z) === x)) by Replacement.apply
      val domChar = thenHave(x ∈ dom(⋃(𝓕)) <=> ∃(z ∈ ⋃(𝓕), fst(z) === x)) by Substitute(dom.definition of (R := ⋃(𝓕)))
      have((z ∈ ⋃(𝓕), fst(z) === x) |- ∃(y, (x, y) ∈ ⋃(𝓕))) subproof {
        assume(z ∈ ⋃(𝓕)); assume(fst(z) === x)
        have(z === (fst(z), snd(z))) by Tautology.from(
          unionIsRel,
          Relations.BasicTheorems.inversion of (R := ⋃(𝓕))
        )
        thenHave((fst(z), snd(z)) ∈ ⋃(𝓕)) by Congruence
        thenHave((x, snd(z)) ∈ ⋃(𝓕)) by Congruence
        thenHave(∃(y, (x, y) ∈ ⋃(𝓕))) by RightExists
      }
      thenHave((z ∈ ⋃(𝓕) /\ (fst(z) === x)) |- ∃(y, (x, y) ∈ ⋃(𝓕))) by Restate
      thenHave(∃(z ∈ ⋃(𝓕), fst(z) === x) |- ∃(y, (x, y) ∈ ⋃(𝓕))) by LeftExists
      thenHave(thesis) by Tautology.fromLastStep(domChar)
    }

    // 6. ∃!(y, (x,y) ∈ ⋃(𝓕)) for x ∈ dom(⋃(𝓕))
    val existsUniqueY = have(x ∈ dom(⋃(𝓕)) |- ∃!(y, (x, y) ∈ ⋃(𝓕))) subproof {
      assume(x ∈ dom(⋃(𝓕)))
      val ex = have(∃(y, (x, y) ∈ ⋃(𝓕))) by Tautology.from(existsY)
      // Build ∀(y, ∀(z, (x,y)∈⋃(𝓕) ∧ (x,z)∈⋃(𝓕) ⇒ y === z)) from unique
      val uniq2 = have(((x, y) ∈ ⋃(𝓕) /\ (x, z) ∈ ⋃(𝓕)) ==> (y === z)) by Tautology.from(unique)
      thenHave(∀(z, ((x, y) ∈ ⋃(𝓕) /\ (x, z) ∈ ⋃(𝓕)) ==> (y === z))) by RightForall
      thenHave(∀(y, ∀(z, ((x, y) ∈ ⋃(𝓕) /\ (x, z) ∈ ⋃(𝓕)) ==> (y === z)))) by RightForall
      val uniqQ = thenHave(∀(y, ∀(z, ((x, y) ∈ ⋃(𝓕)) /\ ((x, z) ∈ ⋃(𝓕)) ==> (y === z)))) by Restate
      have(∃(y, (x, y) ∈ ⋃(𝓕)) /\ ∀(y, ∀(z, (x, y) ∈ ⋃(𝓕) /\ (x, z) ∈ ⋃(𝓕) ==> (y === z)))) by Tautology.from(ex, uniqQ)
      thenHave(thesis) by Tautology.fromLastStep(
        Quantifiers.existsOneAlternativeDefinition of (P := λ(y, (x, y) ∈ ⋃(𝓕)))
      )
    }

    // 7. functionBetween(⋃(𝓕))(dom(⋃(𝓕)))(range(⋃(𝓕)))
    val fb = have(functionBetween(⋃(𝓕))(dom(⋃(𝓕)))(range(⋃(𝓕)))) subproof {
      have(x ∈ dom(⋃(𝓕)) |- ∃!(y, (x, y) ∈ ⋃(𝓕))) by Tautology.from(existsUniqueY)
      thenHave(x ∈ dom(⋃(𝓕)) ==> ∃!(y, (x, y) ∈ ⋃(𝓕))) by Restate
      thenHave(∀(x ∈ dom(⋃(𝓕)), ∃!(y, (x, y) ∈ ⋃(𝓕)))) by RightForall
      thenHave(thesis) by Tautology.fromLastStep(
        functionBetween.definition of (f := ⋃(𝓕), A := dom(⋃(𝓕)), B := range(⋃(𝓕))),
        isRelBetween
      )
    }

    // 8. function(⋃(𝓕))
    have(∃(B, functionBetween(⋃(𝓕))(dom(⋃(𝓕)))(B))) by RightExists(fb)
    thenHave(∃(A, ∃(B, functionBetween(⋃(𝓕))(A)(B)))) by RightExists
    thenHave(thesis) by Tautology.fromLastStep(function.definition of (f := ⋃(𝓕)))
  }

  /**
   * Theorem --- The domain of the unions is the ∪ of the domains.
   */
  val domain = Theorem(
    dom(⋃(𝓕)) === ⋃({ dom(f) | f ∈ 𝓕 })
  ) {
    have(x ∈ { fst(z) | z ∈ f } <=> ∃(z ∈ f, fst(z) === x)) by Replacement.apply
    val `x ∈ dom(f)` = thenHave(x ∈ dom(f) <=> ∃(z ∈ f, fst(z) === x)) by Substitute(dom.definition of (R := f))

    // ⊆ direction: x ∈ dom(⋃(𝓕)) ==> x ∈ ⋃({ dom(f) | f ∈ 𝓕 })
    val forward = have(x ∈ dom(⋃(𝓕)) ==> x ∈ ⋃({ dom(f) | f ∈ 𝓕 })) subproof {
      // Characterization of dom(⋃(𝓕))
      have(x ∈ { fst(z) | z ∈ ⋃(𝓕) } <=> ∃(z ∈ ⋃(𝓕), fst(z) === x)) by Replacement.apply
      val `x ∈ dom(⋃(𝓕))` = thenHave(x ∈ dom(⋃(𝓕)) <=> ∃(z ∈ ⋃(𝓕), fst(z) === x)) by Substitute(dom.definition of (R := ⋃(𝓕)))

      // From z ∈ f: fst(z) ∈ dom(f)
      have(z ∈ f |- fst(z) ∈ { fst(z) | z ∈ f }) by Tautology.from(
        Replacement.map of (x := z, A := f, F := fst)
      )
      val fstInDomf = thenHave(z ∈ f |- fst(z) ∈ dom(f)) by Substitute(dom.definition of (R := f))

      // From f ∈ 𝓕: dom(f) ∈ { dom(f) | f ∈ 𝓕 }
      val domFinSet = have(f ∈ 𝓕 |- dom(f) ∈ { dom(f) | f ∈ 𝓕 }) by Tautology.from(
        Replacement.map of (x := f, A := 𝓕, F := λ(f, dom(f)))
      )

      // Combine: fst(z) ∈ dom(f) ∧ dom(f) ∈ { dom(f) | f ∈ 𝓕 } → ∃y. y ∈ {...} ∧ fst(z) ∈ y
      have((z ∈ f, f ∈ 𝓕) |- dom(f) ∈ { dom(f) | f ∈ 𝓕 } /\ fst(z) ∈ dom(f)) by Tautology.from(
        fstInDomf,
        domFinSet
      )
      thenHave((z ∈ f, f ∈ 𝓕) |- ∃(y, y ∈ { dom(f) | f ∈ 𝓕 } /\ fst(z) ∈ y)) by RightExists
      thenHave((z ∈ f, f ∈ 𝓕) |- fst(z) ∈ ⋃({ dom(f) | f ∈ 𝓕 })) by Tautology.fromLastStep(
        unionAxiom of (x := { dom(f) | f ∈ 𝓕 }, z := fst(z))
      )
      thenHave((z ∈ f, f ∈ 𝓕, fst(z) === x) |- x ∈ ⋃({ dom(f) | f ∈ 𝓕 })) by Congruence
      thenHave((f ∈ 𝓕 /\ (z ∈ f), fst(z) === x) |- x ∈ ⋃({ dom(f) | f ∈ 𝓕 })) by Restate
      thenHave((∃(f, f ∈ 𝓕 /\ (z ∈ f)), fst(z) === x) |- x ∈ ⋃({ dom(f) | f ∈ 𝓕 })) by LeftExists
      thenHave((z ∈ ⋃(𝓕), fst(z) === x) |- x ∈ ⋃({ dom(f) | f ∈ 𝓕 })) by Tautology.fromLastStep(unionAxiom of (x := 𝓕))
      thenHave((z ∈ ⋃(𝓕)) /\ (fst(z) === x) |- x ∈ ⋃({ dom(f) | f ∈ 𝓕 })) by Restate
      thenHave(∃(z, (z ∈ ⋃(𝓕)) /\ (fst(z) === x)) |- x ∈ ⋃({ dom(f) | f ∈ 𝓕 })) by LeftExists
      thenHave(thesis) by Tautology.fromLastStep(`x ∈ dom(⋃(𝓕))`)
    }

    // ⊇ direction: x ∈ ⋃({ dom(f) | f ∈ 𝓕 }) ==> x ∈ dom(⋃(𝓕))
    val backward = have(x ∈ ⋃({ dom(f) | f ∈ 𝓕 }) ==> x ∈ dom(⋃(𝓕))) subproof {
      // z ∈ f, f ∈ 𝓕 → z ∈ ⋃(𝓕) → fst(z) ∈ dom(⋃(𝓕))
      have((z ∈ f, f ∈ 𝓕) |- f ∈ 𝓕 /\ z ∈ f) by Restate
      thenHave((z ∈ f, f ∈ 𝓕) |- ∃(y, y ∈ 𝓕 /\ z ∈ y)) by RightExists
      thenHave((z ∈ f, f ∈ 𝓕) |- z ∈ ⋃(𝓕)) by Tautology.fromLastStep(unionAxiom of (x := 𝓕))
      thenHave((z ∈ f, f ∈ 𝓕) |- fst(z) ∈ { fst(z) | z ∈ ⋃(𝓕) }) by Tautology.fromLastStep(
        Replacement.map of (x := z, A := ⋃(𝓕), F := fst)
      )
      thenHave((z ∈ f, f ∈ 𝓕) |- fst(z) ∈ dom(⋃(𝓕))) by Substitute(dom.definition of (R := ⋃(𝓕)))
      thenHave((z ∈ f, f ∈ 𝓕, fst(z) === x) |- x ∈ dom(⋃(𝓕))) by Congruence
      thenHave(((z ∈ f) /\ (fst(z) === x), f ∈ 𝓕) |- x ∈ dom(⋃(𝓕))) by Restate
      thenHave((∃(z, (z ∈ f) /\ (fst(z) === x)), f ∈ 𝓕) |- x ∈ dom(⋃(𝓕))) by LeftExists
      thenHave((x ∈ dom(f), f ∈ 𝓕) |- x ∈ dom(⋃(𝓕))) by Tautology.fromLastStep(`x ∈ dom(f)`)

      // dom(f) = y, x ∈ y, f ∈ 𝓕 → x ∈ dom(f), f ∈ 𝓕 → x ∈ dom(⋃(𝓕))
      thenHave((dom(f) === y, x ∈ y, f ∈ 𝓕) |- x ∈ dom(⋃(𝓕))) by Congruence
      thenHave(((f ∈ 𝓕) /\ (dom(f) === y), x ∈ y) |- x ∈ dom(⋃(𝓕))) by Restate
      thenHave((∃(f, (f ∈ 𝓕) /\ (dom(f) === y)), x ∈ y) |- x ∈ dom(⋃(𝓕))) by LeftExists
      val fromExists = lastStep

      // y ∈ { dom(f) | f ∈ 𝓕 } <=> ∃f ∈ 𝓕. dom(f) = y
      have(y ∈ { dom(f) | f ∈ 𝓕 } <=> ∃(f ∈ 𝓕, dom(f) === y)) by Replacement.apply
      val repMem = lastStep
      have((y ∈ { dom(f) | f ∈ 𝓕 }) /\ (x ∈ y) |- x ∈ dom(⋃(𝓕))) by Tautology.from(fromExists, repMem)
      thenHave(∃(y, (y ∈ { dom(f) | f ∈ 𝓕 }) /\ (x ∈ y)) |- x ∈ dom(⋃(𝓕))) by LeftExists
      thenHave(thesis) by Tautology.fromLastStep(unionAxiom of (x := { dom(f) | f ∈ 𝓕 }, z := x))
    }

    have(x ∈ dom(⋃(𝓕)) <=> x ∈ ⋃({ dom(f) | f ∈ 𝓕 })) by Tautology.from(forward, backward)
    thenHave(thesis) by Extensionality
  }

}
