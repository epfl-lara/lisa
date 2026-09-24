package lisa.maths

import lisa.SetTheoryLibrary
import org.scalatest.funsuite.AnyFunSuite

/** Check recorded proof errors: initializing a development alone does not fail on them. */
class LibraryProofSuite extends AnyFunSuite:
  private def check(name: String)(initialize: => lisa.Main): Unit =
    test(name):
      initialize
      val errors = SetTheoryLibrary.theorems.all
        .filter(_.fullName.value.startsWith(name + "."))
        .flatMap(theorem => theorem.errors.map(error => s"${theorem.fullName.value}:${error.line.value}: ${error.message}"))
        .toSeq
      assert(errors.isEmpty, errors.mkString("\n"))

  check("lisa.maths.Quantifiers")(lisa.maths.Quantifiers)
  check("lisa.maths.SetTheory.Base.CartesianProduct")(lisa.maths.SetTheory.Base.CartesianProduct)
  check("lisa.maths.SetTheory.Base.Class")(lisa.maths.SetTheory.Base.Class)
  check("lisa.maths.SetTheory.Base.Comprehension")(lisa.maths.SetTheory.Base.Comprehension)
  check("lisa.maths.SetTheory.Base.Difference")(lisa.maths.SetTheory.Base.Difference)
  check("lisa.maths.SetTheory.Base.EmptySet")(lisa.maths.SetTheory.Base.EmptySet)
  check("lisa.maths.SetTheory.Base.FoundationAxiom")(lisa.maths.SetTheory.Base.FoundationAxiom)
  check("lisa.maths.SetTheory.Base.Intersection")(lisa.maths.SetTheory.Base.Intersection)
  check("lisa.maths.SetTheory.Base.Pair")(lisa.maths.SetTheory.Base.Pair)
  check("lisa.maths.SetTheory.Base.PowerSet")(lisa.maths.SetTheory.Base.PowerSet)
  check("lisa.maths.SetTheory.Base.Replacement")(lisa.maths.SetTheory.Base.Replacement)
  check("lisa.maths.SetTheory.Base.Singleton")(lisa.maths.SetTheory.Base.Singleton)
  check("lisa.maths.SetTheory.Base.Subset")(lisa.maths.SetTheory.Base.Subset)
  check("lisa.maths.SetTheory.Base.Symbols")(lisa.maths.SetTheory.Base.Symbols)
  check("lisa.maths.SetTheory.Base.Union")(lisa.maths.SetTheory.Base.Union)
  check("lisa.maths.SetTheory.Base.UnorderedPair")(lisa.maths.SetTheory.Base.UnorderedPair)
  check("lisa.maths.SetTheory.Cardinal.Cardinal")(lisa.maths.SetTheory.Cardinal.Cardinal)
  check("lisa.maths.SetTheory.Cardinal.Universe")(lisa.maths.SetTheory.Cardinal.Universe)
  check("lisa.maths.SetTheory.Cardinal.UniverseRank")(lisa.maths.SetTheory.Cardinal.UniverseRank)
  check("lisa.maths.SetTheory.Functions.BasicTheorems")(lisa.maths.SetTheory.Functions.BasicTheorems)
  check("lisa.maths.SetTheory.Functions.Function")(lisa.maths.SetTheory.Functions.Function)
  check("lisa.maths.SetTheory.Functions.Operations.Composition")(lisa.maths.SetTheory.Functions.Operations.Composition)
  check("lisa.maths.SetTheory.Functions.Operations.Restriction")(lisa.maths.SetTheory.Functions.Operations.Restriction)
  check("lisa.maths.SetTheory.Functions.Operations.Union")(lisa.maths.SetTheory.Functions.Operations.Union)
  check("lisa.maths.SetTheory.Functions.Pi")(lisa.maths.SetTheory.Functions.Pi)
  check("lisa.maths.SetTheory.Functions.Sigma")(lisa.maths.SetTheory.Functions.Sigma)
  check("lisa.maths.SetTheory.Order.BasicTheorems")(lisa.maths.SetTheory.Order.BasicTheorems)
  check("lisa.maths.SetTheory.Order.Examples.EmptyOrder")(lisa.maths.SetTheory.Order.Examples.EmptyOrder)
  check("lisa.maths.SetTheory.Order.Extrema")(lisa.maths.SetTheory.Order.Extrema)
  check("lisa.maths.SetTheory.Order.LowerSet")(lisa.maths.SetTheory.Order.LowerSet)
  check("lisa.maths.SetTheory.Order.OrderIsomorphism")(lisa.maths.SetTheory.Order.OrderIsomorphism)
  check("lisa.maths.SetTheory.Order.PartialOrder")(lisa.maths.SetTheory.Order.PartialOrder)
  check("lisa.maths.SetTheory.Order.TotalOrder")(lisa.maths.SetTheory.Order.TotalOrder)
  check("lisa.maths.SetTheory.Order.WellOrders.InitialSegment")(lisa.maths.SetTheory.Order.WellOrders.InitialSegment)
  check("lisa.maths.SetTheory.Order.WellOrders.OldRecursion")(lisa.maths.SetTheory.Order.WellOrders.OldRecursion)
  check("lisa.maths.SetTheory.Order.WellOrders.WellOrder")(lisa.maths.SetTheory.Order.WellOrders.WellOrder)
  check("lisa.maths.SetTheory.Order.WellOrders.WellOrderedInduction")(lisa.maths.SetTheory.Order.WellOrders.WellOrderedInduction)
  check("lisa.maths.SetTheory.Order.WellOrders.WellOrderedRecursion")(lisa.maths.SetTheory.Order.WellOrders.WellOrderedRecursion)
  check("lisa.maths.SetTheory.Ordinals.Arithmetic")(lisa.maths.SetTheory.Ordinals.Arithmetic)
  check("lisa.maths.SetTheory.Ordinals.Integer")(lisa.maths.SetTheory.Ordinals.Integer)
  check("lisa.maths.SetTheory.Ordinals.Ordinal")(lisa.maths.SetTheory.Ordinals.Ordinal)
  check("lisa.maths.SetTheory.Ordinals.TransfiniteInduction")(lisa.maths.SetTheory.Ordinals.TransfiniteInduction)
  check("lisa.maths.SetTheory.Ordinals.TransfiniteRecursion")(lisa.maths.SetTheory.Ordinals.TransfiniteRecursion)
  check("lisa.maths.SetTheory.Ordinals.TransitiveSet")(lisa.maths.SetTheory.Ordinals.TransitiveSet)
  check("lisa.maths.SetTheory.Relations.BasicTheorems")(lisa.maths.SetTheory.Relations.BasicTheorems)
  check("lisa.maths.SetTheory.Relations.Equivalence")(lisa.maths.SetTheory.Relations.Equivalence)
  check("lisa.maths.SetTheory.Relations.Examples.EmptyRelation")(lisa.maths.SetTheory.Relations.Examples.EmptyRelation)
  check("lisa.maths.SetTheory.Relations.Examples.IdentityRelation")(lisa.maths.SetTheory.Relations.Examples.IdentityRelation)
  check("lisa.maths.SetTheory.Relations.Examples.MembershipRelation")(lisa.maths.SetTheory.Relations.Examples.MembershipRelation)
  check("lisa.maths.SetTheory.Relations.Examples.UniversalRelation")(lisa.maths.SetTheory.Relations.Examples.UniversalRelation)
  check("lisa.maths.SetTheory.Relations.Operations.Closure")(lisa.maths.SetTheory.Relations.Operations.Closure)
  check("lisa.maths.SetTheory.Relations.Operations.Complement")(lisa.maths.SetTheory.Relations.Operations.Complement)
  check("lisa.maths.SetTheory.Relations.Operations.Composition")(lisa.maths.SetTheory.Relations.Operations.Composition)
  check("lisa.maths.SetTheory.Relations.Operations.Converse")(lisa.maths.SetTheory.Relations.Operations.Converse)
  check("lisa.maths.SetTheory.Relations.Operations.Union")(lisa.maths.SetTheory.Relations.Operations.Union)
  check("lisa.maths.SetTheory.Relations.Properties")(lisa.maths.SetTheory.Relations.Properties)
  check("lisa.maths.SetTheory.Relations.Relation")(lisa.maths.SetTheory.Relations.Relation)
  check("lisa.maths.SetTheory.Relations.WellFoundedRelation")(lisa.maths.SetTheory.Relations.WellFoundedRelation)
  check("lisa.maths.SetTheory.SetTheory")(lisa.maths.SetTheory.SetTheory)
  check("lisa.maths.SetTheory.Types.TypeLib")(lisa.maths.SetTheory.Types.TypeLib)
  check("lisa.maths.SetTheory.Types.TypingRules")(lisa.maths.SetTheory.Types.TypingRules)
  check("lisa.maths.SetTheory.Types.TypingTheorems")(lisa.maths.SetTheory.Types.TypingTheorems)

  test("closure and transfinite recursion do not inherit Sorry"):
    for theorem <- Seq(
      lisa.maths.SetTheory.Relations.Operations.Closure.reflexiveClosureValid,
      lisa.maths.SetTheory.Order.WellOrders.WellOrderedRecursion.limitCase,
      lisa.maths.SetTheory.Ordinals.TransfiniteRecursion.transfiniteRecursion
    ) do assert(!theorem.kernel.usesSorry, theorem.fullName.value)
