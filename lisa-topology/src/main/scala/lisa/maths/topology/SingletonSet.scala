package lisa.maths.topology

import lisa.automation.settheory.SetTheoryTactics.*
import lisa.maths.Quantifiers.*

import lisa.automation.kernel.CommonTactics.Definition

import lisa.maths.topology.DiscreteTopology.*
import lisa.maths.topology.Topology.*
import lisa.maths.settheory.*
import lisa.maths.settheory.SetTheory.*
import lisa.maths.settheory.SetTheoryBasics.*
import lisa.automation.kernel.CommonTactics.*
import lisa.maths.settheory.functions.Functionals.*
import lisa.automation.settheory.SetTheoryTactics.UniqueComprehension
import lisa.automation.settheory.SetTheoryTactics.TheConditional

object SingletonSet extends lisa.Main {
  import lisa.maths.settheory.SetTheory.*
  // var defs
  private val x, y, z, a, b, c, t, p, f, s = variable
  private val X, T = variable
  private val S, A, B, Y = variable

  /*
    Theorem: singletonSets exists and it is unique
    exists unique set z whose members are {x} for each x in S
   */
  val singletonSetsUniqueness = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> exists(x, in(x, S) /\ (t === singleton(x)))))
  ) {
    // prove that {x} for each x in S is member of U(SxS)
    val implicationProof = have(exists(x, in(x, S) /\ (t === singleton(x))) ==> in(t, union(cartesianProduct(S, S)))) subproof {

      val elementInSingleton = have(in(x, singleton(x))) subproof {
        have(thesis) by Tautology.from(pairAxiom of (x := x, y := x, z := x))
      }

      val singletonInPowerSet = have(in(x, S) |- in(singleton(x), powerSet(S))) subproof {
        assume(in(x, S))
        thenHave((x === y) |- in(y, S)) by Substitution.ApplyRules(x === y)
        have(in(y, singleton(x)) |- in(y, S)) by Tautology.from(lastStep, singletonHasNoExtraElements)
        thenHave(() |- (!(in(y, singleton(x))), in(y, S))) by RightNot
        thenHave(() |- in(y, singleton(x)) ==> in(y, S)) by Tautology
        thenHave(() |- forall(y, in(y, singleton(x)) ==> in(y, S))) by RightForall
        have(() |- singleton(x) ⊆ S) by Tautology.from(lastStep, subsetAxiom of (z := y, y := S, x := singleton(x)))
        have(thesis) by Tautology.from(lastStep, powerAxiom of (x := singleton(x), y := S))
      }

      val abExist = have((singleton(t) === pair(x, x)) /\ in(x, S) |- ∃(a, ∃(b, (singleton(t) === pair(a, b)) /\ in(a, S) /\ in(b, S)))) subproof {
        have((singleton(t) === pair(x, x)) /\ in(x, S) |- (singleton(t) === pair(x, x)) /\ in(x, S) /\ in(x, S)) by Restate
        thenHave((singleton(t) === pair(x, x)) /\ in(x, S) |- exists(b, (singleton(t) === pair(x, b)) /\ in(x, S) /\ in(b, S))) by RightExists
        thenHave((singleton(t) === pair(x, x)) /\ in(x, S) |- exists(a, exists(b, (singleton(t) === pair(a, b)) /\ in(a, S) /\ in(b, S)))) by RightExists
      }

      // replace the cartesianProduct with its definitions using powerSet and setUnion
      val cartesianInstantiated = have(
        in(singleton(t), cartesianProduct(S, S)) <=> (in(singleton(t), powerSet(powerSet(setUnion(S, S))))
          /\ ∃(a, ∃(b, (singleton(t) === pair(a, b)) /\ in(a, S) /\ in(b, S))))
      ) subproof {
        val instance = have(
          (cartesianProduct(x, y) === cartesianProduct(x, y)) <=> ∀(
            t,
            in(t, cartesianProduct(x, y)) <=> (in(t, powerSet(powerSet(setUnion(x, y))))
              /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))
          )
        ) by InstantiateForall(cartesianProduct(x, y))(cartesianProduct.definition)
        thenHave(
          ∀(
            t,
            in(t, cartesianProduct(x, y)) <=> (in(t, powerSet(powerSet(setUnion(x, y))))
              /\ ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, x) /\ in(b, y))))
          )
        ) by Tautology
        thenHave(
          in(singleton(t), cartesianProduct(x, y)) <=> (in(singleton(t), powerSet(powerSet(setUnion(x, y))))
            /\ ∃(a, ∃(b, (singleton(t) === pair(a, b)) /\ in(a, x) /\ in(b, y))))
        ) by InstantiateForall(singleton(t))
        thenHave(
          forall(
            x,
            in(singleton(t), cartesianProduct(x, y)) <=> (in(singleton(t), powerSet(powerSet(setUnion(x, y))))
              /\ ∃(a, ∃(b, (singleton(t) === pair(a, b)) /\ in(a, x) /\ in(b, y))))
          )
        ) by RightForall
        thenHave(
          in(singleton(t), cartesianProduct(S, y)) <=> (in(singleton(t), powerSet(powerSet(setUnion(S, y))))
            /\ ∃(a, ∃(b, (singleton(t) === pair(a, b)) /\ in(a, S) /\ in(b, y))))
        ) by InstantiateForall(S)
        thenHave(
          forall(
            y,
            in(singleton(t), cartesianProduct(S, y)) <=> (in(singleton(t), powerSet(powerSet(setUnion(S, y))))
              /\ ∃(a, ∃(b, (singleton(t) === pair(a, b)) /\ in(a, S) /\ in(b, y))))
          )
        ) by RightForall
        thenHave(
          in(singleton(t), cartesianProduct(S, S)) <=> (in(singleton(t), powerSet(powerSet(setUnion(S, S))))
            /\ ∃(a, ∃(b, (singleton(t) === pair(a, b)) /\ in(a, S) /\ in(b, S))))
        ) by InstantiateForall(S)
      }

      have(in(x, S) |- in(x, S)) by Restate
      have(in(x, S) |- in(x, setUnion(S, S))) by Tautology.from(lastStep, setUnionMembership of (z := x, x := S, y := S))
      have(in(x, S) |- in(singleton(x), powerSet(setUnion(S, S))) /\ (singleton(singleton(x)) === pair(x, x))) by
        Tautology.from(lastStep, singletonInPowerSet of (S := setUnion(S, S)))
      thenHave((in(x, S), t === singleton(x)) |- in(t, powerSet(setUnion(S, S))) /\ (singleton(t) === pair(x, x))) by
        Substitution.ApplyRules(singleton(x) === t)
      thenHave(in(x, S) /\ (t === singleton(x)) |- in(t, powerSet(setUnion(S, S))) /\ (singleton(t) === pair(x, x))) by Tautology
      have(in(x, S) /\ (t === singleton(x)) |- in(singleton(t), powerSet(powerSet(setUnion(S, S)))) /\ (singleton(t) === pair(x, x))) by
        Tautology.from(lastStep, singletonInPowerSet of (x := t, S := powerSet(setUnion(S, S))))
      have(
        in(x, S) /\ (t === singleton(x)) |- in(singleton(t), powerSet(powerSet(setUnion(S, S)))) /\ in(t, singleton(t))
          /\ ((singleton(t) === pair(x, x)) /\ in(x, S))
      ) by Tautology.from(lastStep, elementInSingleton of (x := t))
      have(
        in(x, S) /\ (t === singleton(x)) |- in(singleton(t), powerSet(powerSet(setUnion(S, S)))) /\ in(t, singleton(t))
          /\ ∃(a, ∃(b, (singleton(t) === pair(a, b)) /\ in(a, S) /\ in(b, S)))
      ) by Tautology.from(lastStep, abExist)
     have(in(x, S) /\ (t === singleton(x)) |- in(singleton(t), cartesianProduct(S, S)) /\ in(t, singleton(t))) by
        Tautology.from(lastStep, cartesianInstantiated)
      thenHave(in(x, S) /\ (t === singleton(x)) |- exists(z, in(z, cartesianProduct(S, S)) /\ in(t, z))) by RightExists
      have((in(x, S) /\ (t === singleton(x))) |- in(t, union(cartesianProduct(S, S)))) by
        Tautology.from(lastStep, unionAxiom of (y := z, x := cartesianProduct(S, S), z := t))
      thenHave(exists(x, (in(x, S) /\ (t === singleton(x)))) |- in(t, union(cartesianProduct(S, S)))) by LeftExists
    }

    // use unique comprehension from original set U(SxS) with the provided predicate and the membership proof
    have(() |- existsOne(z, forall(t, in(t, z) <=> exists(x, in(x, S) /\ (t === singleton(x)))))) by UniqueComprehension.fromOriginalSet(
      union(cartesianProduct(S, S)),
      lambda(t, exists(x, in(x, S) /\ (t === singleton(x)))),
      implicationProof
    )
  }
  val singletonSets = DEF(S) --> The(z, ∀(t, in(t, z) <=> exists(x, in(x, S) /\ (t === singleton(x)))))(singletonSetsUniqueness)

  val singletonSetsMembershipRaw = Theorem(
    in(t, singletonSets(S)) <=> exists(x, ((t === singleton(x)) /\ in(x, S)))
  ) {
    have(∀(t, in(t, singletonSets(S)) <=> exists(x, in(x, S) /\ (t === singleton(x))))) by InstantiateForall(singletonSets(S))(singletonSets.definition)
    thenHave(thesis) by InstantiateForall(t)
  }

  /*
    Theorem: x is member of S iff {x} is member of singletonSets(S)
   */
  val singletonSetsMembership = Theorem(
    in(x, S) <=> in(singleton(x), singletonSets(S))
  ) {
    val form = formulaVariable
    val memb = have(in(t, singletonSets(S)) <=> exists(x, ((t === singleton(x)) /\ in(x, S)))) by Tautology.from(singletonSetsMembershipRaw)
    val forward = have(in(x, S) |- in(singleton(x), singletonSets(S))) subproof {
      assume(in(x, S))
      have(t === singleton(x) |- ((t === singleton(x)) /\ in(x, S))) by Tautology
      thenHave(t === singleton(x) |- exists(x, ((t === singleton(x)) /\ in(x, S)))) by RightExists
      have((t === singleton(x)) ==> in(t, singletonSets(S))) by Tautology.from(lastStep, memb)
      thenHave(forall(t, (t === singleton(x)) ==> in(t, singletonSets(S)))) by RightForall
      thenHave((singleton(x) === singleton(x)) ==> in(singleton(x), singletonSets(S))) by InstantiateForall(singleton(x))
      have(thesis) by Tautology.from(lastStep)
    }
    val backward = have(in(singleton(x), singletonSets(S)) |- in(x, S)) subproof {
      assume(in(singleton(x), singletonSets(S)))
      have(exists(y, ((singleton(x) === singleton(y)) /\ in(y, S))) |- in(x, S)) subproof {
        have(((singleton(x) === singleton(y)) /\ in(y, S)) |- in(x, S)) by Tautology.from(replaceEqualityContainsLeft of (z := S), singletonExtensionality)
        thenHave(thesis) by LeftExists
      }
      have(thesis) by Tautology.from(lastStep, singletonSetsMembershipRaw of (t := singleton(x), y := x))
    }
    have(thesis) by Tautology.from(forward, backward)
  }

  /*
    Theorem: union of sinletonSets(S) is equivalent to S
   */
  val unionSingletonSets = Theorem(union(singletonSets(S)) === S) {

    val elementInSingleton = have(in(x, singleton(x))) by Tautology.from(pairAxiom of (x := x, y := x, z := x))

    // prove that all elements of the union of singletonSets(S) are in S
    val fwd = have(in(x, union(singletonSets(S))) |- in(x, S)) subproof {
      have(in(z, S) |- in(z, S)) by Restate
      thenHave((in(z, S), (x === z)) |- in(x, S)) by Substitution.ApplyRules(x === z)
      have((in(z, S), in(x, singleton(z))) |- in(x, S)) by Tautology.from(lastStep, singletonHasNoExtraElements of (y := x, x := z))
      thenHave((in(z, S), in(x, y), (y === singleton(z))) |- in(x, S)) by Substitution.ApplyRules(y === singleton(z))
      thenHave((in(z, S) /\ (y === singleton(z)), in(x, y)) |- in(x, S)) by Tautology
      thenHave((exists(z, in(z, S) /\ (y === singleton(z))), in(x, y)) |- in(x, S)) by LeftExists
      thenHave(exists(z, in(z, S) /\ (y === singleton(z))) /\ in(x, y) |- in(x, S)) by Tautology
      have(in(y, singletonSets(S)) /\ in(x, y) |- in(x, S)) by Tautology.from(lastStep, singletonSetsMembershipRaw of (x := z, t := y))
      thenHave(exists(y, in(y, singletonSets(S)) /\ in(x, y)) |- in(x, S)) by LeftExists
      have(thesis) by Tautology.from(lastStep, unionAxiom of (z := x, x := singletonSets(S)))
    }

    // prove that all elements in S are in the union of singletonSets(S)
    val bwd = have(in(x, S) |- in(x, union(singletonSets(S)))) subproof {
      assume(in(x, S))
      have(in(x, S) /\ (singleton(x) === singleton(x))) by Restate
      thenHave(exists(y, in(y, S) /\ (singleton(x) === singleton(y)))) by RightExists
      have(in(singleton(x), singletonSets(S)) /\ in(x, singleton(x))) by
        Tautology.from(lastStep, singletonSetsMembershipRaw of (x := y, t := singleton(x)), elementInSingleton)
      thenHave(exists(y, in(y, singletonSets(S)) /\ in(x, y))) by RightExists
      have(thesis) by Tautology.from(lastStep, unionAxiom of (z := x, x := singletonSets(S)))
    }

    have(in(x, union(singletonSets(S))) <=> in(x, S)) by Tautology.from(fwd, bwd)
    thenHave(forall(x, in(x, union(singletonSets(S))) <=> in(x, S))) by RightForall
    have(thesis) by Tautology.from(lastStep, extensionalityAxiom of (z := x, x := union(singletonSets(S)), y := S))
  }

  /*
    Theorem: a topology which contains all singleton sets of the elements of the ground set is the discrete one 
   */
  val ifContainsSingletonIsDiscrete = Theorem(
    (topology(X, T), ∀(x, x ∈ X ==> singleton(x) ∈ T)) |- discreteTopology(X, T)
  ) {
    assume(∀(x, x ∈ X ==> singleton(x) ∈ T), topology(X, T))
    val topo = have(nonEmpty(X) /\ setOfSubsets(X, T) /\ containsExtremes(X, T) /\ containsUnion(T) /\ containsIntersection(T)) by Tautology.from(topology.definition)
    have(forall(Y, (Y ⊆ T) ==> (union(Y) ∈ T))) by Tautology.from(topo, containsUnion.definition)
    val contUnion = thenHave(singletonSets(S) ⊆ T ==> (union(singletonSets(S)) ∈ T)) by InstantiateForall(singletonSets(S))
    have(∀(x, x ∈ X ==> singleton(x) ∈ T)) by Tautology
    val singleDef = thenHave((x ∈ X) ==> (singleton(x) ∈ T)) by InstantiateForall(x)
    have(T === powerSet(X)) subproof {
      // show T subs powerSet(X) (by def of topology)
      val left = have(T ⊆ powerSet(X)) by Tautology.from(topo, setOfSubsets.definition)
      // show powerSet(X) subs T

      // For any S ⊆ X we have S = U{x} -> S ∈ T by unionDef
      have((S ⊆ X) |- S ∈ T) subproof {
        assume(S ⊆ X)
        have(forall(z, in(z, S) ==> in(z, X))) by Tautology.from(subsetAxiom of (x := S, y := X))
        thenHave(in(z, S) ==> in(z, X)) by InstantiateForall(z)
        have(in(z, S) ==> in(singleton(z), T)) by Tautology.from(lastStep, singleDef of (x := z))
        have(in(singleton(z), singletonSets(S)) ==> in(singleton(z), T)) by Tautology.from(lastStep, singletonSetsMembership of (x := z))

        have(((t === singleton(z)) /\ in(z, S)) |- in(t, singletonSets(S)) ==> in(t, T)) by Tautology.from(
          lastStep,
          replaceEqualityContainsLeft of (x := t, y := singleton(z), z := singletonSets(S)),
          replaceEqualityContainsLeft of (x := t, y := singleton(z), z := T)
        )
        thenHave(exists(z, (t === singleton(z)) /\ in(z, S)) |- in(t, singletonSets(S)) ==> in(t, T)) by LeftExists
        have(in(t, singletonSets(S)) ==> in(t, T)) by Tautology.from(lastStep, singletonSetsMembershipRaw of (x := z))
        thenHave(forall(t, in(t, singletonSets(S)) ==> in(t, T))) by RightForall
        have(singletonSets(S) ⊆ T) by Tautology.from(lastStep, subsetAxiom of (x := singletonSets(S), y := T))
        have(union(singletonSets(S)) ∈ T) by Tautology.from(lastStep, contUnion)
        have(thesis) by Tautology.from(lastStep, unionSingletonSets, replaceEqualityContainsLeft of (x := union(singletonSets(S)), y := S, z := T))
      }
      have(in(S, powerSet(X)) ==> in(S, T)) by Tautology.from(lastStep, powerAxiom of (x := S, y := X))
      thenHave(forall(S, in(S, powerSet(X)) ==> in(S, T))) by RightForall
      val right = have(powerSet(X) ⊆ T) by Tautology.from(lastStep, subsetAxiom of (x := powerSet(X), y := T, z := S))

      have(thesis) by Tautology.from(left, right, equalityBySubset of (x := powerSet(X), y := T))
    }
    have(discreteTopology(X, T)) by Tautology.from(lastStep, topo, discreteTopology.definition)
  }
}
