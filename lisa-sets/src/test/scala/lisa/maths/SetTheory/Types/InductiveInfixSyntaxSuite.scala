package lisa.maths.SetTheory.Types

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.InductiveInfixSyntax.SelfRef
import lisa.maths.SetTheory.Types.ADT.InductiveInfixSyntax.inductive
import lisa.maths.SetTheory.Types.ADT.InductiveInfixSyntax.|
import lisa.maths.SetTheory.Types.ADT.ProofChecks._
import lisa.maths.SetTheory.Types.ADT._
import lisa.maths.SetTheory.Types.ADT.interface.ADT
import lisa.maths.SetTheory.Types.ADT.interface.Constructor
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.utils.prooflib.OutputManager
import lisa.utils.prooflib.StringOutputManager
import org.scalatest.funsuite.AnyFunSuite

/**
 * Executes the comma-separated frontend without postfix imports or infix-warning suppression.
 */
class InductiveInfixSyntaxSuite extends AnyFunSuite {
  private given OutputManager = new StringOutputManager

  private val A, B, C, D, E, n, head, tail, x, xs, y, z = variable[Ind]

  private val InfixNat = inductive(
    | zero (),
    | succ (n :: SelfRef)
  )

  private val InfixList = inductive(A)(
    | nil (),
    | cons (head :: A, tail :: SelfRef)
  )

  test("constructor names, binders, and sorts survive infix declarations") {
    val nat: ADT[Ind] = InfixNat
    val successor: Constructor[Ind] = InfixNat.succ
    val list: ADT[Ind >>: Ind] = InfixList
    val cons: Constructor[Ind >>: Ind] = InfixList.cons
    assert(nat.name == "InfixNat")
    assert(nat.constructors.map(_.semantic.name) == Seq("zero", "succ"))
    assert(successor.semantic.variables == Seq(n))
    assert(cons.semantic.variables == Seq(head, tail))
    assert(list.typeVariablesSeq == Seq(A))
    assert(InfixNat.zero eq InfixNat.zero)
    assertDoesNotCompile("InfixNat.zeor")
    assertDoesNotCompile("val invalid: Expr[Ind] = InfixList")
    assertDoesNotCompile("val invalid: Expr[Ind] = InfixList.nil")
  }

  test("declarations are expressions and the registered owners of their constructors") {
    summon[InductiveInfixSyntax.Declaration[Ind] <:< ADT[Ind]]
    summon[InductiveInfixSyntax.Declaration[Ind] <:< Expr[Ind]]
    summon[InductiveInfixSyntax.Declaration[Ind >>: Ind] <:< Expr[Ind >>: Ind]]
    val nat: Expr[Ind] = InfixNat
    val list: Expr[Ind >>: Ind] = InfixList
    assert(nat eq InfixNat)
    assert(list eq InfixList)
    assert(ADT.getADT(InfixNat.id).exists(_ eq InfixNat))
    assert(ADT.getADT(InfixList.name).exists(_ eq InfixList))
    assert(InfixNat.zero.adt eq InfixNat)
    assert(InfixList.cons.adt eq InfixList)
    assert(InfixNat.constructors.head eq InfixNat.zero)
  }

  test("typing and generated constructor theorems execute") {
    val singleton = InfixList.cons(InfixNat) * InfixNat.zero * InfixList.nil(InfixNat)
    val typing = Theorem.generated(singleton :: InfixList(InfixNat)) {
      have(thesis) by Typecheck.prove
    }
    assert(!typing.hasErrorsOrSorry)
    assert(!InfixNat.succ.injectivity.hasErrorsOrSorry)
    assert(!InfixNat.disjointness(InfixNat.zero, InfixNat.succ).hasErrorsOrSorry)
    assert(!InfixNat.elim.hasErrorsOrSorry && !InfixList.induction.hasErrorsOrSorry)
  }

  test("recursive definitions, computation, and induction use the generated members") {
    val infixListCopy = recFun(InfixList, InfixList(A)) { self =>
      Case(InfixList.nil):
        InfixList.nil(A)
      Case(InfixList.cons, head, tail):
        InfixList.cons(A) * head * (self * tail)
    }
    val computation = Theorem.generated(infixListCopy(A) * InfixList.nil(A) === InfixList.nil(A)) {
      have(thesis) by Restate.from(infixListCopy.elim(InfixList.nil).of(A))
    }
    val identity = Theorem.generated(xs :: InfixList(A) |- infixListCopy(A) * xs === xs) {
      have(thesis) by Induction(xs, InfixList.specialize(A)) {
        Case(InfixList.nil) subproof {
          have(thesis) by Restate.from(infixListCopy.elim(InfixList.nil).of(A))
        }
        Case(InfixList.cons, head, tail) subproof {
          lisa.maths.SetTheory.SetTheory.assume(head :: A, tail :: InfixList(A), infixListCopy(A) * tail === tail)
          val step = have(infixListCopy(A) * (InfixList.cons(A) * head * tail) === InfixList.cons(A) * head * (infixListCopy(A) * tail)) by
            Tautology.from(infixListCopy.elim(InfixList.cons).of(A))
          have(thesis) by Congruence.from(step)
        }
      }
    }
    assert(!computation.hasErrorsOrSorry && !identity.hasErrorsOrSorry && !infixListCopy.intro.hasErrorsOrSorry)
  }

  test("field tuples preserve order and recursive fields use every parameter") {
    val InfixTree = inductive((A, B))(
      | leaf (head :: A, tail :: B),
      | node (x :: SelfRef, y :: SelfRef, z :: SelfRef)
    )
    assert(InfixTree.typeVariablesSeq == Seq(A, B))
    assert(InfixTree.node.semantic.variables == Seq(x, y, z))
    val leaf = InfixTree.leaf(InfixNat, InfixNat) * InfixNat.zero * InfixNat.zero
    val typing = Theorem.generated(InfixTree.node(InfixNat, InfixNat) * leaf * leaf * leaf :: InfixTree(InfixNat, InfixNat)) {
      have(thesis) by Typecheck.prove
    }
    assert(!typing.hasErrorsOrSorry)
  }

  test("empty declarations and all supported parameter arities retain their sorts") {
    val InfixEmpty = inductive()
    val InfixEmpty3 = inductive((A, B, C))()
    val InfixEmpty4 = inductive((A, B, C, D))()
    val InfixEmpty5 = inductive((A, B, C, D, E))()
    val three: ADT[Ind >>: Ind >>: Ind >>: Ind] = InfixEmpty3
    val four: ADT[Ind >>: Ind >>: Ind >>: Ind >>: Ind] = InfixEmpty4
    val five: ADT[Ind >>: Ind >>: Ind >>: Ind >>: Ind >>: Ind] = InfixEmpty5
    assert(three.typeVariablesSeq == Seq(A, B, C))
    assert(four.typeVariablesSeq == Seq(A, B, C, D))
    assert(five.typeVariablesSeq == Seq(A, B, C, D, E))
    assert(!InfixEmpty.elim.hasErrorsOrSorry && !five.elim.hasErrorsOrSorry)
  }

  test("invalid fields and constructor names are rejected at compile time") {
    assertDoesNotCompile("inductive(| same(), | same())")
    assertDoesNotCompile("inductive(| induction())")
    assertDoesNotCompile("inductive(| elim())")
    assertDoesNotCompile("inductive(| constructors())")
    assertDoesNotCompile("inductive(| name())")
    assertDoesNotCompile("inductive(| id())")
    assertDoesNotCompile("inductive(| sort())")
    assertDoesNotCompile("inductive(| apply())")
    assertDoesNotCompile("inductive(| selectDynamic())")
    assertDoesNotCompile("inductive(| bad(42))")
    assertDoesNotCompile("inductive(A)(| bad(head :: A, 42))")
    assertDoesNotCompile("inductive(A)(| bad(head :: A, ()))")
    assertDoesNotCompile("inductive(| bad(InfixNat.zero :: SelfRef))")
    assertDoesNotCompile("inductive(if true then | yes() else | no())")
    assertDoesNotCompile("inductive(|.applyDynamic(n.toString)(()))")
    assertDoesNotCompile("inductive(A)(| bad(x :: SelfRef(A)))")
  }

  test("duplicate binders and undeclared or duplicate parameters fail before proof construction") {
    intercept[IllegalArgumentException] {
      val InfixDuplicateFields = inductive(| pair (x :: SelfRef, x :: SelfRef))
    }
    intercept[IllegalArgumentException] {
      val InfixUndeclaredType = inductive(A)(| bad (x :: B))
    }
    intercept[IllegalArgumentException] {
      val InfixDuplicateParameters = inductive((A, A))(| empty ())
    }
  }

  test("recursive markers remain distinct from identically named type parameters") {
    val parameter = Variable[Ind]("inductiveSelf")
    val InfixMarkerList = inductive(parameter)(
      | nil (),
      | cons (head :: parameter, tail :: SelfRef)
    )
    val value = InfixMarkerList.cons(InfixNat) * InfixNat.zero * InfixMarkerList.nil(InfixNat)
    val typing = Theorem.generated(value :: InfixMarkerList(InfixNat)) {
      have(thesis) by Typecheck.prove
    }
    assert(!typing.hasErrorsOrSorry)
  }

  test("indexed type parameters retain their identity") {
    val indexed = Variable[Ind](Identifier("A", 1))
    val InfixIndexedBox = inductive(indexed)(| box (x :: indexed))
    assert(InfixIndexedBox.typeVariablesSeq == Seq(indexed))
    val typing = Theorem.generated(x :: indexed |- InfixIndexedBox.box(indexed) * x :: InfixIndexedBox(indexed)) {
      have(thesis) by Typecheck.prove
    }
    assert(!typing.hasErrorsOrSorry)
  }

  test("indexed field binders retain their identity") {
    val indexed = Variable[Ind](Identifier("x", 1))
    val InfixIndexedField = inductive(A)(| box (indexed :: A))
    assert(InfixIndexedField.box.semantic.variables == Seq(indexed))
    val typing = Theorem.generated(indexed :: A |- InfixIndexedField.box(A) * indexed :: InfixIndexedField(A)) {
      have(thesis) by Typecheck.prove
    }
    assert(!typing.hasErrorsOrSorry)
  }

  test("declarations can be used during their enclosing object's initialization") {
    object Enclosing {
      val InfixLocalNat = inductive(| zero (), | succ (n :: SelfRef))
      val typing = Theorem.generated(InfixLocalNat.succ * InfixLocalNat.zero :: InfixLocalNat) {
        have(thesis) by Typecheck.prove
      }
    }
    assert(!Enclosing.typing.hasErrorsOrSorry)
  }
}
