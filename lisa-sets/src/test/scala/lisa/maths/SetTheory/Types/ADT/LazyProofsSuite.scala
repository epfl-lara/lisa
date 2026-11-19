package lisa.maths.SetTheory.Types.ADT

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT._
import lisa.maths.SetTheory.Types.ADT.library.bool
import lisa.maths.SetTheory.Types.ADT.library.cons
import lisa.maths.SetTheory.Types.ADT.library.list
import lisa.maths.SetTheory.Types.ADT.library.nil
import lisa.maths.SetTheory.Types.ADT.library.tru
import lisa.utils.prooflib.OutputManager
import org.scalatest.funsuite.AnyFunSuite

/**
 * Checks that proof accessors build only requested theorems and retain their results.
 */
class LazyProofsSuite extends AnyFunSuite:
  private given OutputManager = new OutputManager:
    val stringWriter = new java.io.StringWriter
    def finishOutput(exception: Exception): Nothing = throw exception

  private val A, head, tail, inner = variable[Ind]
  private def registered(name: String): Boolean = lisa.SetTheoryLibrary.theory.getTheorem(name).isDefined

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
    assert(!leafInjectivity.withSorry)
    assert(registered(s"${leaf.name}/injectivity"))
    assert(!registered(s"${node.name}/injectivity"))
    assert(!registered(s"${declaration.name}/induction"))

    val induction = declaration.induction
    val nodeInjectivity = node.injectivity
    val elimination = declaration.elim
    assert(!induction.withSorry && !nodeInjectivity.withSorry && !elimination.withSorry)
    assert(registered(s"${declaration.name}/induction"))
    assert(registered(s"${node.name}/injectivity"))
    val last = lisa.SetTheoryLibrary.last
    assert(declaration.induction eq induction)
    assert(leaf.injectivity eq leafInjectivity)
    assert(node.injectivity eq nodeInjectivity)
    assert(declaration.elim eq elimination)
    assert(lisa.SetTheoryLibrary.last == last)

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
    assert(!requested.withSorry && !nullary.withSorry && !total.withSorry)
    val last = lisa.SetTheoryLibrary.last
    assert(lazySimpleEquations.elim(cons) eq requested)
    assert(lazySimpleEquations.elimTotal eq total)
    assert(lisa.SetTheoryLibrary.last == last)

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
    assert(!branch.withSorry && !group.withSorry)

    val foreignConstructor = tru
    val foreignClause = clauses.head.copy(payload = bool: Expr[Ind])
    val last = lisa.SetTheoryLibrary.last
    assert(lazyNestedEquations.elim(clauses(1)) eq branch)
    assert(lazyNestedEquations.elim(cons) eq group)
    intercept[IllegalArgumentException](lazyNestedEquations.elim(foreignClause))
    intercept[IllegalArgumentException](lazyNestedEquations.semantic.elim(foreignClause))
    intercept[IllegalArgumentException](lazyNestedEquations.elim(foreignConstructor))
    intercept[IllegalArgumentException](lazyNestedEquations.semantic.elim(foreignConstructor.semantic))
    assert(lisa.SetTheoryLibrary.last == last)
    clauses.foreach(clause => assert(!lazyNestedEquations.elim(clause).withSorry))
    assert(!lazyNestedEquations.elimTotal.withSorry)
    assert(registered(s"${lazyNestedEquations.name}/case/0"))
    assert(registered(s"${lazyNestedEquations.name}/elimination/cons/2"))
    assert(registered(s"${lazyNestedEquations.name}/constructor/cons"))
    assert(registered(s"${lazyNestedEquations.name}/cases"))

  test("empty datatypes and functions retain their lazy total theorems"):
    val empty = adt("lazyEmptyDatatype", Seq.empty)
    assert(!registered(s"${empty.name}/induction"))
    val lazyEmptyFunction = fun(empty, ∅) {}
    val total = lazyEmptyFunction.elimTotal
    assert(!empty.induction.withSorry && !empty.elim.withSorry)
    assert(registered(s"${empty.name}/induction"))
    assert(!lazyEmptyFunction.intro.withSorry && !total.withSorry)
    val last = lisa.SetTheoryLibrary.last
    assert(lazyEmptyFunction.elimTotal eq total)
    assert(lisa.SetTheoryLibrary.last == last)
