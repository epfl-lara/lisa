package lisa.maths.SetTheory.Types.ADT

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.ProofChecks._
import lisa.maths.SetTheory.Types.ADT._
import lisa.maths.SetTheory.Types.ADT.library.bool
import lisa.maths.SetTheory.Types.ADT.library.cons
import lisa.maths.SetTheory.Types.ADT.library.list
import lisa.maths.SetTheory.Types.ADT.library.nil
import lisa.maths.SetTheory.Types.ADT.library.tru
import lisa.utils.prooflib.OutputManager
import lisa.utils.prooflib.StringOutputManager
import org.scalatest.funsuite.AnyFunSuite

/**
 * Checks that proof accessors build only requested theorems and retain their results.
 */
class LazyProofsSuite extends AnyFunSuite:
  private given OutputManager = new StringOutputManager

  private val A, head, tail, inner = variable[Ind]
  private def registered(name: String): Boolean = lisa.SetTheoryLibrary.theorems.getFull(name).isDefined

  test("induction and each constructor's injectivity are deferred until requested"):
    val declaration = adt(
      "lazyProofDatatype",
      "A",
      Seq(
        ("leaf", Seq("value" -> "A")),
        ("node", Seq("left" -> SelfRef, "right" -> SelfRef))
      )
    )
    val Seq(leaf, node) = declaration.constructors: @unchecked
    assert(!registered(s"${declaration.name}/induction"))
    assert(!registered(s"${leaf.name}/injectivity"))
    assert(!registered(s"${node.name}/injectivity"))

    val leafInjectivity = leaf.injectivity
    assert(!leafInjectivity.hasErrorsOrSorry)
    assert(registered(s"${leaf.name}/injectivity"))
    assert(!registered(s"${node.name}/injectivity"))
    assert(!registered(s"${declaration.name}/induction"))

    val induction = declaration.induction
    val nodeInjectivity = node.injectivity
    val elimination = declaration.elim
    assert(!induction.hasErrorsOrSorry && !nodeInjectivity.hasErrorsOrSorry && !elimination.hasErrorsOrSorry)
    assert(registered(s"${declaration.name}/induction"))
    assert(registered(s"${node.name}/injectivity"))
    val last = lisa.SetTheoryLibrary.theorems.all.size
    assert(declaration.induction eq induction)
    assert(leaf.injectivity eq leafInjectivity)
    assert(node.injectivity eq nodeInjectivity)
    assert(declaration.elim eq elimination)
    assert(lisa.SetTheoryLibrary.theorems.all.size == last)

  test("single-clause constructor access reuses that branch without forcing other equations"):
    val lazySimpleEquations = fun(A)(list.specialize(A), list(A)) {
      Case(nil):
        nil(A)
      Case(cons, head, tail):
        nil(A)
    }
    val clauses = lazySimpleEquations.semantic.clauses
    def semanticEquation(index: Int) = s"${lazySimpleEquations.name}/case/$index"
    assert(clauses.indices.forall(i => !registered(semanticEquation(i))))
    assert(!registered(s"${lazySimpleEquations.name}/cases"))
    assert(!registered(s"${lazySimpleEquations.name}/eliminationTotal"))

    val requested = lazySimpleEquations.elim(cons)
    assert(requested eq lazySimpleEquations.elim(clauses(1)))
    assert(lazySimpleEquations.semantic.elim(cons.semantic) eq lazySimpleEquations.semantic.elim(clauses(1)))
    assert(registered(semanticEquation(1)))
    assert(!registered(semanticEquation(0)))
    assert(!registered(s"${lazySimpleEquations.name}/elimination/nil/0"))
    assert(!registered(s"${lazySimpleEquations.name}/cases"))
    assert(!registered(s"${lazySimpleEquations.name}/eliminationTotal"))

    val nullary = lazySimpleEquations.elim(nil)
    val total = lazySimpleEquations.elimTotal
    assert(registered(semanticEquation(0)))
    assert(registered(s"${lazySimpleEquations.name}/elimination/nil/0"))
    assert(registered(s"${lazySimpleEquations.name}/cases"))
    assert(registered(s"${lazySimpleEquations.name}/eliminationTotal"))
    assert(!requested.hasErrorsOrSorry && !nullary.hasErrorsOrSorry && !total.hasErrorsOrSorry)
    val last = lisa.SetTheoryLibrary.theorems.all.size
    assert(lazySimpleEquations.elim(cons) eq requested)
    assert(lazySimpleEquations.elimTotal eq total)
    assert(lisa.SetTheoryLibrary.theorems.all.size == last)

  test("nested constructor groups force only their clauses and reject foreign requests without proofs"):
    val lazyNestedEquations = fun(A)(list.specialize(A), list(A)) {
      Case(nil):
        nil(A)
      Case(cons, head, nil(A)):
        nil(A)
      Case(cons, head, cons(A) * tail * inner):
        nil(A)
    }
    val clauses = lazyNestedEquations.semantic.clauses
    val branch = lazyNestedEquations.elim(clauses(1))
    assert(!registered(s"${lazyNestedEquations.name}/case/0"))
    assert(!registered(s"${lazyNestedEquations.name}/case/2"))
    val group = lazyNestedEquations.elim(cons)
    assert(registered(s"${lazyNestedEquations.name}/constructor/cons"))
    assert(!registered(s"${lazyNestedEquations.name}/cases"))
    assert(registered(s"${lazyNestedEquations.name}/case/2"))
    assert(!registered(s"${lazyNestedEquations.name}/case/0"))
    assert(!registered(s"${lazyNestedEquations.name}/elimination/cons/2"))
    assert(!branch.hasErrorsOrSorry && !group.hasErrorsOrSorry)

    val foreignConstructor = tru
    val foreignClause = clauses.head.copy(payload = bool: Expr[Ind])
    val last = lisa.SetTheoryLibrary.theorems.all.size
    assert(lazyNestedEquations.elim(clauses(1)) eq branch)
    assert(lazyNestedEquations.elim(cons) eq group)
    intercept[IllegalArgumentException](lazyNestedEquations.elim(foreignClause))
    intercept[IllegalArgumentException](lazyNestedEquations.semantic.elim(foreignClause))
    intercept[IllegalArgumentException](lazyNestedEquations.elim(foreignConstructor))
    intercept[IllegalArgumentException](lazyNestedEquations.semantic.elim(foreignConstructor.semantic))
    assert(lisa.SetTheoryLibrary.theorems.all.size == last)
    clauses.foreach(clause => assert(!lazyNestedEquations.elim(clause).hasErrorsOrSorry))
    assert(!lazyNestedEquations.elimTotal.hasErrorsOrSorry)
    assert(registered(s"${lazyNestedEquations.name}/case/0"))
    assert(registered(s"${lazyNestedEquations.name}/elimination/cons/2"))
    assert(registered(s"${lazyNestedEquations.name}/constructor/cons"))
    assert(registered(s"${lazyNestedEquations.name}/cases"))

  test("empty datatypes and functions retain their lazy total theorems"):
    val empty = adt("lazyEmptyDatatype", Seq.empty)
    assert(!registered(s"${empty.name}/induction"))
    val lazyEmptyFunction = fun(empty, ∅) {}
    val total = lazyEmptyFunction.elimTotal
    assert(!empty.induction.hasErrorsOrSorry && !empty.elim.hasErrorsOrSorry)
    assert(registered(s"${empty.name}/induction"))
    assert(!lazyEmptyFunction.intro.hasErrorsOrSorry && !total.hasErrorsOrSorry)
    val last = lisa.SetTheoryLibrary.theorems.all.size
    assert(lazyEmptyFunction.elimTotal eq total)
    assert(lisa.SetTheoryLibrary.theorems.all.size == last)
