package lisa.maths.SetTheory.Types

import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.ProofChecks._
import lisa.maths.SetTheory.Types.ADT._
import lisa.maths.SetTheory.Types.ADT.interface.ADT
import lisa.maths.SetTheory.Types.ADT.interface.ADTFunction
import lisa.maths.SetTheory.Types.ADT.interface.RecFunction
import lisa.maths.SetTheory.Types.ADT.interface.SpecializedADT
import lisa.maths.SetTheory.Types.ADT.library.bool
import lisa.maths.SetTheory.Types.ADT.library.box
import lisa.maths.SetTheory.Types.ADT.library.cons
import lisa.maths.SetTheory.Types.ADT.library.fals
import lisa.maths.SetTheory.Types.ADT.library.list
import lisa.maths.SetTheory.Types.ADT.library.nat
import lisa.maths.SetTheory.Types.ADT.library.nil
import lisa.maths.SetTheory.Types.ADT.library.pack
import lisa.maths.SetTheory.Types.ADT.library.product
import lisa.maths.SetTheory.Types.ADT.library.succ
import lisa.maths.SetTheory.Types.ADT.library.tru
import lisa.maths.SetTheory.Types.ADT.library.void
import lisa.maths.SetTheory.Types.ADT.library.zero
import lisa.maths.SetTheory.Types.ADT.library.{pair => productPair}
import lisa.maths.SetTheory.Types.ADT.library.{union => unionType}
import lisa.maths.SetTheory.Types.ADT.support.semantics.DefinedSymbol
import lisa.maths.SetTheory.Types.ADT.syntax.AST.ConstructorArg
import lisa.maths.SetTheory.Types.ADT.syntax.AST.TypeArg
import lisa.utils.prooflib.OutputManager
import lisa.utils.prooflib.StringOutputManager
import org.scalatest.funsuite.AnyFunSuite

/**
 * Executes generated ADT proofs for specialization, nested patterns, and binder hygiene.
 */
class ADTRegressionSuite extends AnyFunSuite:
  private given OutputManager = new StringOutputManager

  private val A, hd, hd2, tl, k, q = variable[Ind]

  test("induction case bodies remain user proofs and recover without stopping later cases"):
    var continued = false
    val proposition = variable[Prop]
    val theorem = Theorem.generated(k :: nat |- proposition) {
      have(thesis) by Induction(k, nat) {
        Case(zero) subproof {
          assert(!currentProof.isTactic)
          have(thesis) by ((_: Sequent) => lisa.utils.prooflib.ProofCarrier.Failure("case failure"))
          continued = true
        }
        Case(succ, hd) subproof {
          assert(!currentProof.isTactic && continued)
          have(thesis) by Tautology
        }
      }
    }
    assert(continued && theorem.thm.usesSorry)
    assert(theorem.errors.size == 1 && theorem.errors.head.message == "case failure")

  test("declare ordinary function parameters independently of a monomorphic domain"):
    val B = variable[Ind]
    val regressionEmptyLists: ADTFunction[Ind >>: Ind] = fun(B)(nat, list(B)) {
      Case(zero):
        nil(B)
      Case(succ, k):
        nil(B)
    }
    assert(regressionEmptyLists.typeVariablesSeq == Seq(B))
    assert(regressionEmptyLists.sort == list.sort)
    assert(!regressionEmptyLists.intro.hasErrorsOrSorry)
    val typing = Theorem.generated(regressionEmptyLists(bool) :: (nat ->: list(bool))) {
      have(thesis) by Restate.from(regressionEmptyLists.intro.of(bool))
    }
    val computation = Theorem.generated(regressionEmptyLists(bool) * zero === nil(bool)) {
      have(thesis) by Restate.from(regressionEmptyLists.elim(zero).of(bool))
    }
    assert(!typing.hasErrorsOrSorry && !computation.hasErrorsOrSorry)

  test("declare recursive function parameters independently of a monomorphic domain"):
    val B = variable[Ind]
    val regressionRecursiveEmptyLists: RecFunction[Ind >>: Ind] = recFun(B)(nat, list(B)) { self =>
      Case(zero):
        nil(B)
      Case(succ, k):
        self * k
    }
    assert(regressionRecursiveEmptyLists.typeVariablesSeq == Seq(B))
    assert(!regressionRecursiveEmptyLists.intro.hasErrorsOrSorry)
    val computation = Theorem.generated(regressionRecursiveEmptyLists(bool) * (succ * zero) === nil(bool)) {
      val step = have(regressionRecursiveEmptyLists(bool) * (succ * zero) === regressionRecursiveEmptyLists(bool) * zero) by
        Tautology.from(regressionRecursiveEmptyLists.elim(succ).of(bool).of(k := zero), zero.intro)
      have(thesis) by Congruence.from(step, regressionRecursiveEmptyLists.elim(zero).of(bool))
    }
    assert(!computation.hasErrorsOrSorry)

  test("preserve explicit parameter order and distinct input and output parameters"):
    val B = variable[Ind]
    val regressionDifferentTypes: ADTFunction[Ind >>: Ind >>: Ind] = fun((B, A))(list.specialize(A), list(B)) {
      Case(nil):
        nil(B)
      Case(cons, hd, tl):
        nil(B)
    }
    val regressionDifferentTypesRec: RecFunction[Ind >>: Ind >>: Ind] = recFun((B, A))(list.specialize(A), list(B)) { self =>
      Case(nil):
        nil(B)
      Case(cons, hd, tl):
        self * tl
    }
    assert(regressionDifferentTypes.typeVariablesSeq == Seq(B, A))
    assert(regressionDifferentTypesRec.typeVariablesSeq == Seq(B, A))
    assert(regressionDifferentTypes.sort == unionType.sort)
    val typing = Theorem.generated(regressionDifferentTypes(bool, nat) :: (list(nat) ->: list(bool))) {
      have(thesis) by Tactics.Typecheck.prove
    }
    val recursiveTyping = Theorem.generated(regressionDifferentTypesRec(bool, nat) :: (list(nat) ->: list(bool))) {
      have(thesis) by Tactics.Typecheck.prove
    }
    assert(!typing.hasErrorsOrSorry && !recursiveTyping.hasErrorsOrSorry)

  test("specializing the domain does not rewrite an independent parameter with the same name"):
    val regressionIndependentA = fun(A)(list.specialize(bool), list(A)) {
      Case(nil):
        nil(A)
      Case(cons, hd, tl):
        nil(A)
    }
    val regressionIndependentARec = recFun(A)(list.specialize(bool), list(A)) { self =>
      Case(nil):
        nil(A)
      Case(cons, hd, nil(bool)):
        nil(A)
      Case(cons, hd, cons(bool) * hd2 * tl):
        self * tl
    }
    val computation = Theorem.generated(regressionIndependentA(nat) * nil(bool) === nil(nat)) {
      have(thesis) by Restate.from(regressionIndependentA.elim(nil).of(nat))
    }
    val recursiveComputation = Theorem.generated(regressionIndependentARec(nat) * nil(bool) === nil(nat)) {
      have(thesis) by Restate.from(regressionIndependentARec.elim(nil).of(nat))
    }
    assert(!computation.hasErrorsOrSorry && !recursiveComputation.hasErrorsOrSorry)

  test("preserve parameters in nested patterns and recursion on compound specialized domains"):
    val regressionParametricNestedUnbox = recFun(A)(box.specialize(list(A)), list(A)) { _ =>
      Case(pack, nil(A)):
        nil(A)
      Case(pack, cons(A) * hd * tl):
        tl
    }
    assert(!regressionParametricNestedUnbox.intro.hasErrorsOrSorry)
    assert(!regressionParametricNestedUnbox.elim(Case(pack, cons(A) * hd * tl)).hasErrorsOrSorry)
    val regressionListsLength = recFun(A)(list.specialize(list(A)), nat) { self =>
      Case(nil):
        zero
      Case(cons, hd, tl):
        succ * (self * tl)
    }
    val computation = Theorem.generated(regressionListsLength(bool) * (cons(list(bool)) * nil(bool) * nil(list(bool))) === succ * zero) {
      val step = have(
        regressionListsLength(bool) * (cons(list(bool)) * nil(bool) * nil(list(bool))) === succ * (regressionListsLength(bool) * nil(list(bool)))
      ) by Tautology.from(regressionListsLength.elim(cons).of(bool).of(hd := nil(bool), tl := nil(list(bool))), nil.intro.of(bool), nil.intro.of(list(bool)))
      have(thesis) by Congruence.from(step, regressionListsLength.elim(nil).of(bool))
    }
    assert(!computation.hasErrorsOrSorry)

  test("allow a partially specialized domain with fewer function parameters"):
    val inl = unionType.constructors(0)
    val inr = unionType.constructors(1)
    val regressionPartialSpecialization: ADTFunction[Ind >>: Ind] = fun(A)(unionType.specialize(bool, A), bool) {
      Case(inl, hd):
        hd
      Case(inr, hd):
        fals
    }
    val typing = Theorem.generated(regressionPartialSpecialization(nat) :: (unionType(bool, nat) ->: bool)) {
      have(thesis) by Restate.from(regressionPartialSpecialization.intro.of(nat))
    }
    assert(!typing.hasErrorsOrSorry)

  test("reject undeclared return type parameters before proof generation"):
    val B = variable[Ind]
    val ordinary = intercept[IllegalArgumentException] {
      val regressionUndeclaredReturn = fun(nat, list(B)) {
        Case(zero):
          nil(B)
        Case(succ, k):
          nil(B)
      }
    }
    val recursive = intercept[IllegalArgumentException] {
      val regressionUndeclaredReturnRec = recFun(nat, list(B)) { self =>
        Case(zero):
          nil(B)
        Case(succ, k):
          self * k
      }
    }
    for error <- Seq(ordinary, recursive) do assert(error.getMessage.contains("undeclared free variables: B"))

  test("reject undeclared body variables, duplicate parameters, and parameter shadowing"):
    val B = variable[Ind]
    val body = intercept[IllegalArgumentException] {
      val regressionUndeclaredBody = fun(nat, nat) {
        Case(zero):
          B
        Case(succ, k):
          zero
      }
    }
    assert(body.getMessage.contains("undeclared free variables: B"))
    val duplicate = intercept[IllegalArgumentException] {
      val regressionDuplicateParameters = fun((B, B))(nat, list(B)) {
        Case(zero):
          nil(B)
        Case(succ, k):
          nil(B)
      }
    }
    assert(duplicate.getMessage.contains("duplicate parameters"))
    val shadow = intercept[IllegalArgumentException] {
      val regressionShadowedParameter = fun(A)(box.specialize(A), A) {
        Case(pack, A):
          A
      }
    }
    assert(shadow.getMessage.contains("shadows a parameter"))

  private def checkTypeArgumentArity(arguments: Seq[Expr[Ind]], applications: Seq[Seq[Expr[Ind]] => Expr[Ind]]): Unit =
    for application <- applications do
      assert(application(arguments).sort == nat.sort)
      val invalidArguments = Seq(arguments.dropRight(1), arguments :+ nat).filter(_.size != arguments.size)
      for invalid <- invalidArguments do
        val error = intercept[IllegalArgumentException](application(invalid))
        assert(error.getMessage.contains(s"expects ${arguments.size}"))
        assert(error.getMessage.contains(s"got ${invalid.size}"))

  test("check type argument arity in ADT applications and specializations"):
    for datatype <- Seq(nat, list, unionType) do
      checkTypeArgumentArity(
        datatype.typeVariablesSeq.map(_ => nat),
        Seq(
          datatype.termAt,
          datatype.applySeq,
          args => datatype(args*),
          args => datatype.specialize(args*).term
        )
      )

  test("check constructor type arguments while allowing curried value application"):
    for constructor <- Seq(succ, cons, unionType.constructors.head) do
      checkTypeArgumentArity(
        constructor.typeVariablesSeq.map(_ => nat),
        Seq(
          constructor.termAt,
          constructor.applySeq,
          args => constructor(args*),
          args => constructor.specialize(args*).term
        )
      )
    val partiallyApplied = cons.specialize(nat)(zero)
    assert(partiallyApplied.sort == nat.sort)
    val typing = Theorem.generated(partiallyApplied :: (list(nat) ->: list(nat))) {
      have(thesis) by Tactics.Typecheck.prove
    }
    assert(!typing.hasErrorsOrSorry)

  test("check defined symbol parameters independently of the result sort"):
    val value = new DefinedSymbol("regressionArityValue", Seq(A), A)
    val proposition = new DefinedSymbol("regressionArityProposition", Seq(A), A === A)
    val predicate = new DefinedSymbol("regressionArityPredicate", Seq(A), λ(hd, hd ∈ A))
    val closed = new DefinedSymbol("regressionArityClosed", Seq.empty, ∅)
    for (symbol, arguments, resultSort) <- Seq(
        (value, Seq(nat), A.sort),
        (proposition, Seq(nat), (A === A).sort),
        (predicate, Seq(nat), λ(hd, hd ∈ A).sort),
        (closed, Seq.empty, ∅.sort)
      )
    do
      assert(symbol.term(arguments).sort == resultSort)
      for invalid <- Seq(arguments.dropRight(1), arguments :+ nat).filter(_.size != arguments.size) do
        val error = intercept[IllegalArgumentException](symbol.term(invalid))
        assert(error.getMessage.contains(s"expects ${arguments.size}"))
        assert(error.getMessage.contains(s"got ${invalid.size}"))

  test("look up nested equations independently of binder names"):
    val regressionNestedPredecessor = fun(nat, nat) {
      Case(zero):
        zero
      Case(succ, zero):
        zero
      Case(succ, succ * k):
        k
    }
    checkTypeArgumentArity(
      Seq.empty,
      Seq(
        regressionNestedPredecessor.termAt,
        regressionNestedPredecessor.applySeq,
        args => regressionNestedPredecessor(args*),
        regressionNestedPredecessor.semantic.term
      )
    )
    val original = regressionNestedPredecessor.elim(Case(succ, succ * k))
    val renamed = regressionNestedPredecessor.elim(Case(succ, succ * q))
    assert(renamed == original)
    assert(!renamed.hasErrorsOrSorry)
    val outer = regressionNestedPredecessor.patternFor(Case(succ, succ * q)).binders.head
    val computation = Theorem.generated(q :: nat |- regressionNestedPredecessor * (succ * (succ * q)) === q) {
      lisa.utils.prooflib.ProofHelpers.assume(q :: nat)
      have(succ * q :: nat) by Tactics.Typecheck.prove
      have(thesis) by Tautology.from(lastStep, renamed.of(k := q, outer := succ * q))
    }
    assert(!computation.hasErrorsOrSorry)

    for query <- Seq(
        Case(pack, succ * q),
        Case(succ, pack(nat) * q),
        Case(succ, succ * (succ * q)),
        Case(succ, succ),
        Case(succ, succ * q * hd)
      )
    do intercept[IllegalArgumentException](regressionNestedPredecessor.elim(query))

  test("preserve type arguments and a bijection of all pattern binders during lookup"):
    val regressionLookupList = fun(list, nat) {
      Case(nil):
        zero
      Case(cons, hd, nil(A)):
        zero
      Case(cons, hd, cons(A) * hd2 * tl):
        succ * zero
    }
    val original = regressionLookupList.elim(Case(cons, hd, cons(A) * hd2 * tl))
    assert(regressionLookupList.elim(Case(cons, k, cons(A) * q * hd)) == original)
    assert(regressionLookupList.elim(Case(cons, hd2, cons(A) * hd * tl)) == original)
    assert(!original.hasErrorsOrSorry)

    val B = variable[Ind]
    for query <- Seq(
        Case(cons, k, cons(B) * q * hd),
        Case(cons, k, cons(bool) * q * hd),
        Case(cons, hd, cons(A) * hd * tl),
        Case(cons, k, cons(A) * q * q),
        Case(cons, k, cons(A) * q),
        Case(cons, k, cons(A) * q * hd * tl),
        Case(nil, k)
      )
    do intercept[IllegalArgumentException](regressionLookupList.elim(query))

  test("construct a polymorphic recursion seed from a data-carrying constructor"):
    val regressionRecursiveUnbox = recFun(box, A) { _ =>
      Case(pack, hd):
        hd
    }
    assert(!regressionRecursiveUnbox.intro.hasErrorsOrSorry)
    val computation = Theorem.generated(hd :: A |- regressionRecursiveUnbox(A) * (pack(A) * hd) === hd) {
      have(thesis) by Restate.from(regressionRecursiveUnbox.elim(pack).of(A))
    }
    assert(!computation.hasErrorsOrSorry)

  test("construct a recursion seed with empty domain and codomain"):
    val regressionEmptyUnbox = recFun(box.specialize(∅), ∅) { _ =>
      Case(pack, hd):
        hd
    }
    assert(!regressionEmptyUnbox.intro.hasErrorsOrSorry)
    assert(!regressionEmptyUnbox.elim(pack).hasErrorsOrSorry)

  test("recurse on trees whose leaves carry the only target inhabitant"):
    val tree = adt(
      "regressionSeedTree",
      "A",
      Seq(
        ("leaf", Seq(("value", "A"))),
        ("node", Seq(("left", "regressionSeedTree"), ("right", "regressionSeedTree")))
      )
    )
    val leaf = tree.constructors(0)
    val node = tree.constructors(1)
    val regressionLeftmost = recFun(tree, A) { self =>
      Case(leaf, hd):
        hd
      Case(node, k, q):
        self * k
    }
    assert(!regressionLeftmost.intro.hasErrorsOrSorry)
    assert(!regressionLeftmost.elim(leaf).hasErrorsOrSorry)
    assert(!regressionLeftmost.elim(node).hasErrorsOrSorry)

  test("construct a recursion seed through nested base patterns"):
    val regressionNestedUnbox = recFun(box.specialize(list(bool)), list(bool)) { _ =>
      Case(pack, nil(bool)):
        nil(bool)
      Case(pack, cons(bool) * hd * tl):
        tl
    }
    assert(!regressionNestedUnbox.intro.hasErrorsOrSorry)
    assert(!regressionNestedUnbox.elim(Case(pack, cons(bool) * hd * tl)).hasErrorsOrSorry)

  test("recurse through several nested binders of the same constructor"):
    val tree = adt(
      "regressionNestedBinary",
      Seq(
        ("leaf", Seq.empty),
        ("node", Seq(("left", "regressionNestedBinary"), ("right", "regressionNestedBinary")))
      )
    )
    val leaf = tree.constructors(0)
    val node = tree.constructors(1)
    val regressionNestedBranches = recFun(tree, tree) { self =>
      Case(leaf):
        leaf
      Case(node, leaf, tl):
        self * tl
      Case(node, node * k * q, tl):
        node * (self * k) * (self * q)
    }
    val pairOfLeaves = node * leaf * leaf
    val query = Case(node, node * k * q, tl)
    val pattern = regressionNestedBranches.patternFor(query)
    val witnesses: Seq[Expr[Ind]] = Seq(pairOfLeaves, leaf, leaf, leaf)
    val substitutions = pattern.binders.zip(witnesses).map((v, term) => v := term)
    val computation = Theorem.generated(regressionNestedBranches * (node * pairOfLeaves * leaf) === pairOfLeaves) {
      val pairTyped = have(pairOfLeaves :: tree) by Tactics.Typecheck.prove
      val step = have(
        regressionNestedBranches * (node * pairOfLeaves * leaf) ===
          node * (regressionNestedBranches * leaf) * (regressionNestedBranches * leaf)
      ) by Tautology.from(regressionNestedBranches.elim(query).of(substitutions*), pairTyped, leaf.intro)
      have(thesis) by Congruence.from(step, regressionNestedBranches.elim(leaf))
    }
    assert(!computation.hasErrorsOrSorry && !regressionNestedBranches.intro.hasErrorsOrSorry)

  test("specializing a payload to an ADT does not introduce an induction hypothesis"):
    var checked = false
    val reflexivity = Theorem.generated(k :: box(nat) |- k === k) {
      have(thesis) by Induction(k, box.specialize(nat)) {
        Case(pack, hd) subproof {
          assert(thesis.left.exists(isSame(_, hd :: nat)))
          assert(!thesis.left.exists(isSame(_, hd === hd)))
          checked = true
          have(thesis) by Tautology
        }
      }
    }
    assert(checked && !reflexivity.hasErrorsOrSorry)

  test("define recursion from Void into the empty set"):
    val regressionVoidRecursion = recFun(void, ∅) { _ => () }
    assert(!regressionVoidRecursion.intro.hasErrorsOrSorry)

  test("define recursion with only recursive constructors and an empty target"):
    val loop = adt("regressionSeedLoop", Seq(("again", Seq(("tail", "regressionSeedLoop")))))
    val again = loop.constructors.head
    val regressionEmptyRecursion = recFun(loop, ∅) { self =>
      Case(again, k):
        self * k
    }
    assert(!regressionEmptyRecursion.intro.hasErrorsOrSorry)
    assert(!regressionEmptyRecursion.elim(again).hasErrorsOrSorry)

  test("define an ordinary function with empty domain and codomain"):
    val regressionOrdinaryEmptyUnbox = fun(box.specialize(∅), ∅) {
      Case(pack, hd):
        hd
    }
    val typing = Theorem.generated(regressionOrdinaryEmptyUnbox :: (box(∅) ->: ∅)) {
      have(thesis) by Tactics.Typecheck.prove
    }
    val computation = Theorem.generated(hd :: ∅ |- regressionOrdinaryEmptyUnbox * (pack(∅) * hd) === hd) {
      have(thesis) by Restate.from(regressionOrdinaryEmptyUnbox.elim(pack))
    }
    assert(!typing.hasErrorsOrSorry && !computation.hasErrorsOrSorry)

  test("define an ordinary function from Void into the empty set"):
    val regressionOrdinaryVoid = fun(void, ∅) { () }
    val typing = Theorem.generated(regressionOrdinaryVoid :: (void ->: ∅)) {
      have(thesis) by Tactics.Typecheck.prove
    }
    assert(!typing.hasErrorsOrSorry)
    assert(!regressionOrdinaryVoid.elimTotal.hasErrorsOrSorry)

  test("freshen the hidden self-reference against ordinary pattern binders"):
    val payload = Variable[Ind]("regressionHiddenSelfRecSelf")
    val regressionHiddenSelf = fun(box.specialize(nat), nat) {
      Case(pack, payload):
        payload
    }
    val computation = Theorem.generated(regressionHiddenSelf * (pack(nat) * zero) === zero) {
      have(thesis) by Tautology.from(regressionHiddenSelf.elim(pack).of(payload := zero), zero.intro)
    }
    assert(!computation.hasErrorsOrSorry)

  test("do not interpret an undeclared ordinary body variable as recursive self-reference"):
    val unbound = Variable[Ind]("regressionHiddenFreeRecSelf")
    rejectWithoutRegistration("undeclared free variables: regressionHiddenFreeRecSelf") {
      val regressionHiddenFree = fun(nat, nat) {
        Case(zero):
          unbound
        Case(succ, k):
          zero
      }
    }

  test("define a plain function on a specialized ADT"):
    val regressionUnbox = fun(box.specialize(bool), bool) {
      Case(pack, hd):
        hd
    }
    checkTypeArgumentArity(
      Seq.empty,
      Seq(
        regressionUnbox.termAt,
        regressionUnbox.applySeq,
        args => regressionUnbox(args*),
        regressionUnbox.semantic.term
      )
    )
    assert(!regressionUnbox.intro.hasErrorsOrSorry)
    assert(regressionUnbox.typeVariablesSeq.isEmpty)
    val computation = Theorem.generated(regressionUnbox * (pack(bool) * tru) === tru) {
      have(thesis) by Tautology.from(regressionUnbox.elim(pack).of(hd := tru), tru.intro)
    }
    assert(!computation.hasErrorsOrSorry)

  test("define a recursive function with plain specialized patterns"):
    val regressionLength = recFun(list.specialize(bool), nat) { self =>
      Case(nil):
        zero
      Case(cons, hd, tl):
        succ * (self * tl)
    }
    checkTypeArgumentArity(
      Seq.empty,
      Seq(
        regressionLength.termAt,
        regressionLength.applySeq,
        args => regressionLength(args*),
        regressionLength.semantic.term
      )
    )
    assert(!regressionLength.intro.hasErrorsOrSorry)
    assert(!regressionLength.elim(cons).hasErrorsOrSorry)
    assert(regressionLength.elim(Case(cons, k, q)) == regressionLength.elim(Case(cons, hd, tl)))
    for args <- Seq(Seq(hd), Seq(hd, tl, k), Seq(hd, hd)) do intercept[IllegalArgumentException](regressionLength.elim(Case(cons, args*)))

  test("allow opaque type parameters at nested pattern leaves"):
    val regressionListShape = fun(list, nat) {
      Case(nil):
        zero
      Case(cons, hd, nil(A)):
        zero
      Case(cons, hd, cons(A) * hd2 * tl):
        zero
    }
    assert(!regressionListShape.intro.hasErrorsOrSorry)
    assert(!regressionListShape.elim(Case(cons, hd, cons(A) * hd2 * tl)).hasErrorsOrSorry)

  test("allow function types at nested pattern leaves"):
    val regressionFunctionListShape = fun(list.specialize(nat ->: nat), nat) {
      Case(nil):
        zero
      Case(cons, hd, nil(nat ->: nat)):
        zero
      Case(cons, hd, cons(nat ->: nat) * hd2 * tl):
        zero
    }
    assert(!regressionFunctionListShape.intro.hasErrorsOrSorry)

  test("recurse through a nested pattern with opaque payloads"):
    val regressionNestedLength = recFun(list, nat) { self =>
      Case(nil):
        zero
      Case(cons, hd, nil(A)):
        succ * zero
      Case(cons, hd, cons(A) * hd2 * tl):
        succ * (succ * (self * tl))
    }
    assert(!regressionNestedLength.intro.hasErrorsOrSorry)
    assert(!regressionNestedLength.elim(Case(cons, hd, cons(A) * hd2 * tl)).hasErrorsOrSorry)
    assert(
      regressionNestedLength.elim(Case(cons, k, cons(A) * q * hd)) ==
        regressionNestedLength.elim(Case(cons, hd, cons(A) * hd2 * tl))
    )

  test("retain different specializations of a repeated nested constructor"):
    val regressionDoubleUnbox = fun(A)(box.specialize(box(A)), A) {
      Case(pack, pack(A) * hd):
        hd
    }
    val original = regressionDoubleUnbox.elim(Case(pack, pack(A) * hd))
    assert(regressionDoubleUnbox.elim(Case(pack, pack(A) * q)) == original)
    val B = variable[Ind]
    intercept[IllegalArgumentException](regressionDoubleUnbox.elim(Case(pack, pack(B) * q)))
    intercept[IllegalArgumentException](regressionDoubleUnbox.elim(Case(pack, pack(box(A)) * q)))
    val outer = regressionDoubleUnbox.patternFor(Case(pack, pack(A) * hd)).binders.head
    val computation = Theorem.generated(hd :: A |- regressionDoubleUnbox(A) * (pack(box(A)) * (pack(A) * hd)) === hd) {
      lisa.utils.prooflib.ProofHelpers.assume(hd :: A)
      have(pack(A) * hd :: box(A)) by Tactics.Typecheck.prove
      have(thesis) by Tautology.from(lastStep, original.of(A).of(outer := pack(A) * hd))
    }
    assert(!regressionDoubleUnbox.intro.hasErrorsOrSorry && !computation.hasErrorsOrSorry)

  test("preserve case bodies when nested cases inspect both constructor fields"):
    val regressionSecondBoolean = fun(product.specialize(bool, bool), bool) {
      Case(productPair, fals, tru):
        tru
      Case(productPair, tru, fals):
        fals
      Case(productPair, tru, tru):
        tru
      Case(productPair, fals, fals):
        fals
    }
    for (left, right) <- Seq((fals, tru), (tru, fals), (tru, tru), (fals, fals)) do
      val query = Case(productPair, left, right)
      val binders = regressionSecondBoolean.patternFor(query).binders
      val equation = regressionSecondBoolean.elim(query)
      val computation = Theorem.generated(regressionSecondBoolean * (productPair(bool, bool) * left * right) === right) {
        have(thesis) by Tautology.from(equation.of(binders(0) := left, binders(1) := right), tru.intro, fals.intro)
      }
      assert(!computation.hasErrorsOrSorry)

  test("prove all computations of an eight-leaf decision tree with reordered clauses"):
    val booleans: Seq[Expr[Ind]] = Seq(fals, tru)
    val cases = Seq((1, 1, 1), (0, 0, 0), (1, 0, 1), (0, 1, 0), (1, 1, 0), (0, 0, 1), (1, 0, 0), (0, 1, 1))
    val regressionBooleanParity = fun(product.specialize(bool, product(bool, bool)), bool) {
      cases.foreach { (first, second, third) =>
        Case(productPair, booleans(first), productPair(bool, bool) * booleans(second) * booleans(third))(
          booleans((first + second + third) % 2)
        )
      }
    }
    for (first, second, third) <- cases.reverse do
      val left = booleans(first)
      val right = productPair(bool, bool) * booleans(second) * booleans(third)
      val expected = booleans((first + second + third) % 2)
      val query = Case(productPair, left, right)
      val binders = regressionBooleanParity.patternFor(query).binders
      val equation = regressionBooleanParity.elim(query)
      val computation = Theorem.generated(regressionBooleanParity * (productPair(bool, product(bool, bool)) * left * right) === expected) {
        val rightTyped = have(right :: product(bool, bool)) by Tactics.Typecheck.prove
        have(thesis) by Tautology.from(equation.of(binders(0) := left, binders(1) := right), rightTyped, tru.intro, fals.intro)
      }
      assert(!computation.hasErrorsOrSorry)
    assert(!regressionBooleanParity.intro.hasErrorsOrSorry)

  test("retain a fresh outer binder across nested induction callbacks and assembly"):
    val inner = Variable[Ind]("succ/arg0")
    val premise = variable[Prop]
    val contextual = Theorem.generated((k :: nat, premise) |- premise) {
      have(thesis) by Induction(k, nat) {
        Case(succ, succ * inner) subproof { have(thesis) by Hypothesis }
        Case(zero) subproof { have(thesis) by Hypothesis }
        Case(succ, zero) subproof { have(thesis) by Hypothesis }
      }
    }
    assert(!contextual.hasErrorsOrSorry)

  test("reconstruct whole-subtree binders after other clauses inspect the same field"):
    val elementType = Variable[Ind]("fv0")
    val xs = Variable[Ind]("scrutX")
    val tail = Variable[Ind]("bsf0")
    val regressionWholeSubtree = fun(elementType)(product.specialize(list(elementType), bool), list(elementType)) {
      Case(productPair, cons(elementType) * hd * tail, fals):
        tail
      Case(productPair, xs, tru):
        xs
      Case(productPair, nil(elementType), fals):
        nil(elementType)
    }
    val empty = nil(bool)
    val singleton = cons(bool) * tru * empty
    val checks: Seq[(Case, Expr[Ind], Expr[Ind], Seq[Expr[Ind]], Expr[Ind])] = Seq(
      (Case(productPair, xs, tru), empty, tru, Seq(empty, tru), empty),
      (Case(productPair, xs, tru), singleton, tru, Seq(singleton, tru), singleton),
      (Case(productPair, nil(elementType), fals), empty, fals, Seq(empty, fals), empty),
      (Case(productPair, cons(elementType) * hd * tail, fals), singleton, fals, Seq(singleton, fals, tru, empty), empty)
    )
    for (query, input, flag, witnesses, result) <- checks do
      val pattern = regressionWholeSubtree.patternFor(query)
      val equation = regressionWholeSubtree.elim(query)
      val substitutions = pattern.binders.zip(witnesses).map((v, term) => v := term)
      val computation = Theorem.generated(regressionWholeSubtree(bool) * (productPair(list(bool), bool) * input * flag) === result) {
        val emptyTyped = have(empty :: list(bool)) by Tactics.Typecheck.prove
        val singletonTyped = have(singleton :: list(bool)) by Tactics.Typecheck.prove
        have(thesis) by Tautology.from(equation.of(bool).of(substitutions*), emptyTyped, singletonTyped, tru.intro, fals.intro)
      }
      assert(!computation.hasErrorsOrSorry)
    assert(!regressionWholeSubtree.intro.hasErrorsOrSorry)

  test("assemble reordered multi-field induction with whole-subtree binders and ambient variables"):
    val scrutinee = Variable[Ind]("scrutX")
    val elementType = Variable[Ind]("bsf0")
    val ambient = Variable[Ind]("fv0")
    val xs = variable[Ind]
    val premise = ambient === elementType
    val contextual = Theorem.generated((scrutinee :: product(list(elementType), bool), premise) |- premise) {
      have(thesis) by Induction(scrutinee, product.specialize(list(elementType), bool)) {
        Case(productPair, cons(elementType) * hd * tl, fals) subproof { have(thesis) by Hypothesis }
        Case(productPair, xs, tru) subproof { have(thesis) by Hypothesis }
        Case(productPair, nil(elementType), fals) subproof { have(thesis) by Hypothesis }
      }
    }
    assert(!contextual.hasErrorsOrSorry)

  test("assemble nontrivial induction with inner pattern binders"):
    val arg = Variable[Ind]("succ/arg0")
    val nonzero = Theorem.generated(k :: nat |- !(succ * k === zero)) {
      have(thesis) by Induction(k, nat) {
        Case(zero) subproof {
          have(zero :: nat) by Tactics.Typecheck.prove
          have(thesis) by Tautology.from(lastStep, nat.disjointness(succ, zero).of(zero))
        }
        Case(succ, zero) subproof {
          lisa.utils.prooflib.ProofHelpers.assume(arg :: nat)
          have(succ * arg :: nat) by Tactics.Typecheck.prove
          have(thesis) by Tautology.from(lastStep, nat.disjointness(succ, zero).of(succ * arg))
        }
        Case(succ, succ * q) subproof {
          lisa.utils.prooflib.ProofHelpers.assume(arg :: nat)
          have(succ * arg :: nat) by Tactics.Typecheck.prove
          have(thesis) by Tautology.from(lastStep, nat.disjointness(succ, zero).of(succ * arg))
        }
      }
    }
    assert(!nonzero.hasErrorsOrSorry)

  test("retain ambient assumptions during nested induction"):
    val premise = variable[Prop]
    val contextual = Theorem.generated((k :: nat, premise) |- premise) {
      have(thesis) by Induction(k, nat) {
        Case(zero) subproof { have(thesis) by Hypothesis }
        Case(succ, zero) subproof { have(thesis) by Hypothesis }
        Case(succ, succ * q) subproof { have(thesis) by Hypothesis }
      }
    }
    assert(!contextual.hasErrorsOrSorry)

  test("eliminate several inner binders with opaque types during induction"):
    val arg = Variable[Ind]("cons/arg1")
    val membership = Theorem.generated(k :: list(A) |- k :: list(A)) {
      have(thesis) by Induction(k, list.specialize(A)) {
        Case(nil) subproof { have(thesis) by Tautology.from(nil.intro.of(A)) }
        Case(cons, hd, nil(A)) subproof {
          have(thesis) by Tautology.from(cons.introApp.of(cons.semantic.variables(0) := hd, cons.semantic.variables(1) := arg))
        }
        Case(cons, hd, cons(A) * hd2 * tl) subproof {
          have(thesis) by Tautology.from(cons.introApp.of(cons.semantic.variables(0) := hd, cons.semantic.variables(1) := arg))
        }
      }
    }
    assert(!membership.hasErrorsOrSorry)

  test("freshen constructor proof placeholders against argument names"):
    val regressionC = adt("regressionC", "A", Seq(("wrap", Seq(("c", "A")))))
    assert(!regressionC.constructors.head.intro.hasErrorsOrSorry)
    assert(!regressionC.constructors.head.injectivity.hasErrorsOrSorry)

  test("freshen constructor extensionality variables against argument names"):
    val regressionPoints = adt("regressionPoints", "A", Seq(("wrap", Seq(("curriedfn", "A"), ("pointarg0", "A")))))
    assert(!regressionPoints.constructors.head.intro.hasErrorsOrSorry)
    assert(!regressionPoints.constructors.head.injectivity.hasErrorsOrSorry)

  test("keep the two constructor argument tuples disjoint"):
    val regressionCopies = adt("regressionCopies", "A", Seq(("wrap", Seq(("c", "A"), ("c2", "A")))))
    val constructor = regressionCopies.constructors.head
    assert(constructor.semantic.variables.toSet.intersect(constructor.semantic.variables2.toSet).isEmpty)
    assert(!constructor.intro.hasErrorsOrSorry)
    assert(!constructor.injectivity.hasErrorsOrSorry)

  test("keep constructor binders distinct from type parameters"):
    val regressionParameter = adt("regressionParameter", "A", Seq(("wrap", Seq(("A", "A")))))
    assert(!regressionParameter.constructors.head.intro.hasErrorsOrSorry)
    assert(!regressionParameter.constructors.head.injectivity.hasErrorsOrSorry)

  for argName <- Seq("a", "b", "d", "f", "g", "k", "r", "s", "t", "x", "y", "z", "α", "β") do
    test(s"constructor argument $argName does not capture proof variables"):
      val declaration = adt(s"regressionName/$argName", "A", Seq(("wrap", Seq((argName, "A")))))
      assert(!declaration.constructors.head.intro.hasErrorsOrSorry)
      assert(!declaration.constructors.head.injectivity.hasErrorsOrSorry)

  private def rejectWithoutRegistration(message: String)(declaration: => Any): Unit =
    val language = lisa.SetTheoryLibrary.theory.language.toSet
    val last = lisa.SetTheoryLibrary.theorems.all.size
    val registered = ADT.allADTs.toSet
    val error = intercept[IllegalArgumentException](declaration)
    assert(error.getMessage.contains(message), error.getMessage)
    assert(lisa.SetTheoryLibrary.theory.language.toSet == language)
    assert(lisa.SetTheoryLibrary.theorems.all.size == last)
    assert(ADT.allADTs.toSet == registered)

  test("reject undeclared ADT parameters through both argument forms and allow corrected declarations"):
    val invalidTypes: Seq[String | ConstructorArg] = Seq("Missing", TypeArg("Missing"))
    for (invalid, index) <- invalidTypes.zipWithIndex do
      val name = s"regressionUndeclaredADT$index"
      rejectWithoutRegistration("argument 'value' refers to undeclared type parameter 'Missing'") {
        adt(name, "A", Seq(("wrap", Seq(("value", invalid)))))
      }
      assert(ADT.getADT(name).isEmpty)
      val corrected = adt(name, "A", Seq(("wrap", Seq(("value", TypeArg("A"))))))
      assert(!corrected.constructors.head.intro.hasErrorsOrSorry)

  test("validate all constructor names and binders before generating proofs"):
    rejectWithoutRegistration("duplicate constructor names") {
      adt("regressionDuplicateConstructors", Seq(("wrap", Seq.empty), ("wrap", Seq.empty)))
    }
    rejectWithoutRegistration("regressionLateDuplicate/second has duplicate argument names") {
      adt("regressionLateDuplicate", "A", Seq(("first", Seq.empty), ("second", Seq(("value", "A"), ("value", "A")))))
    }
    rejectWithoutRegistration("empty constructor name") {
      adt("regressionEmptyConstructor", Seq((" ", Seq.empty)))
    }
    rejectWithoutRegistration("empty argument name") {
      adt("regressionEmptyArgument", "A", Seq(("wrap", Seq(("", "A")))))
    }
    rejectWithoutRegistration("empty type variable name") {
      adt("regressionEmptyParameter", "", Seq.empty)
    }
    rejectWithoutRegistration("duplicate type variables") {
      adt("regressionDuplicateADTParameters", ("A", "A"), Seq.empty)
    }
    rejectWithoutRegistration("nonempty name") {
      adt("", Seq.empty)
    }

  private def rejectFunctionCases(domain: SpecializedADT[?], cases: Seq[Case], message: String): Unit =
    rejectWithoutRegistration(message) {
      val regressionInvalidFunctionCases = fun(domain, nat) {
        cases.foreach(c => c(zero))
      }
    }
    rejectWithoutRegistration(message) {
      val regressionInvalidRecursiveCases = recFun(domain, nat) { _ =>
        cases.foreach(c => c(zero))
      }
    }

  test("reject wrong constructors and exact outer and nested arity mismatches"):
    val cases = Seq(
      Case(tru) -> "is not a constructor",
      Case(succ) -> "expected 1 value argument(s), got 0",
      Case(succ, k, q) -> "expected 1 value argument(s), got 2",
      Case(succ, succ) -> "argument 1: Constructor nat/succ expects 1 value argument(s), got 0",
      Case(succ, succ * k * q) -> "expects 1 value argument(s), got 2",
      Case(succ, zero * k) -> "expects 0 value argument(s), got 1",
      Case(succ, tru) -> "argument 1: bool/tru is not a constructor"
    )
    for (invalid, message) <- cases do rejectFunctionCases(nat, Seq(Case(zero), invalid), message)

  test("reject unsupported nested expressions instead of interpreting them as binders"):
    for term <- Seq(∅, k * q) do rejectFunctionCases(nat, Seq(Case(zero), Case(succ, term)), "argument 1: Unsupported pattern")

  test("check nested constructor specialization and preserve opaque binder types"):
    rejectFunctionCases(list.specialize(bool), Seq(Case(nil), Case(cons, hd, nil(nat))), "argument 2: constructor type arguments")
    rejectFunctionCases(list.specialize(bool), Seq(Case(nil), Case(cons, hd, nil.asInstanceOf[Expr[Ind]])), "expects 1 type argument(s), got 0")
    rejectFunctionCases(list.specialize(A), Seq(Case(nil), Case(cons, zero, tl)), "argument 1: cannot match constructor nat/zero at non-ADT type A")
    rejectFunctionCases(list.specialize(nat ->: nat), Seq(Case(nil), Case(cons, zero, tl)), "at non-ADT type")

  test("reject repeated binders across outer and nested pattern arguments"):
    val cases = Seq(Case(cons, hd, hd), Case(cons, hd, cons(bool) * hd * tl), Case(cons, hd, cons(bool) * tl * tl))
    for invalid <- cases do rejectFunctionCases(list.specialize(bool), Seq(Case(nil), invalid), "repeated pattern binder")

  test("reject missing and overlapping unconditional cases before proof generation"):
    rejectFunctionCases(nat, Seq(Case(zero)), "Case for nat/succ is missing")
    rejectFunctionCases(nat, Seq(Case(zero), Case(zero), Case(succ, k)), "Overlapping unconditional cases for nat/zero")

  test("reject missing nested constructor combinations before registering functions"):
    rejectFunctionCases(nat, Seq(Case(zero), Case(succ, zero)), "missing")
    rejectFunctionCases(
      product.specialize(bool, bool),
      Seq(
        Case(productPair, tru, tru),
        Case(productPair, fals, tru),
        Case(productPair, fals, fals)
      ),
      "missing"
    )

  test("reject overlapping nested cases independently of clause order"):
    val cases = Seq(Case(nil), Case(cons, hd, nil(bool)), Case(cons, hd, tl))
    for ordered <- Seq(cases, cases.reverse) do rejectFunctionCases(list.specialize(bool), ordered, "overlap")

  test("distinguish nested constructors with the same short names in different datatypes"):
    val leftType = adt("regressionDecisionLeft", Seq(("off", Seq.empty), ("on", Seq.empty)))
    val rightType = adt("regressionDecisionRight", Seq(("off", Seq.empty), ("on", Seq.empty)))
    val leftOff = leftType.constructors(0)
    val leftOn = leftType.constructors(1)
    val rightOff = rightType.constructors(0)
    val rightOn = rightType.constructors(1)
    val regressionDistinctConstructors = fun(product.specialize(leftType, rightType), bool) {
      Case(productPair, leftOn, rightOff):
        fals
      Case(productPair, leftOff, rightOn):
        tru
      Case(productPair, leftOn, rightOn):
        tru
      Case(productPair, leftOff, rightOff):
        fals
    }
    for (left, right, result) <- Seq(
        (leftOff, rightOff, fals),
        (leftOff, rightOn, tru),
        (leftOn, rightOff, fals),
        (leftOn, rightOn, tru)
      )
    do
      val query = Case(productPair, left, right)
      val binders = regressionDistinctConstructors.patternFor(query).binders
      val equation = regressionDistinctConstructors.elim(query)
      val computation = Theorem.generated(regressionDistinctConstructors * (productPair(leftType, rightType) * left * right) === result) {
        have(thesis) by Tautology.from(equation.of(binders(0) := left, binders(1) := right), left.intro, right.intro)
      }
      assert(!computation.hasErrorsOrSorry)
    assert(!regressionDistinctConstructors.intro.hasErrorsOrSorry)

  for (description, conclusions) <- Seq(
      "empty" -> Set.empty[Expr[Prop]],
      "multiple" -> Set(k === k, k === q)
    )
  do
    test(s"reject induction goals with $description conclusions before invoking case callbacks"):
      val checked = Theorem.generated(k === k) { proof ?=>
        for assumptions <- Seq(Set.empty[Expr[Prop]], Set(k :: nat)) do
          val goal = Sequent(assumptions, conclusions)
          assert(Induction.inferArguments(goal, None, None).isEmpty)
          assert(Induction.inferArguments(goal, Some(k), Some(nat.specialize())).isEmpty)
          for tactic <- Seq(Induction(), Induction(k, nat)) do
            var entered = false
            val result = tactic { entered = true }(goal)
            assert(!result.isValid)
            assert((result match { case lisa.utils.prooflib.ProofCarrier.Failure(message) => message.contains("exactly one formula on the right"); case _ => false }))
            assert(!entered)
        have(thesis) by RightRefl
      }
      assert(!checked.hasErrorsOrSorry)

  test("validate induction patterns before executing their subproofs"):
    val cases = Seq(
      Case(tru) -> "is not a constructor",
      Case(nil, hd) -> "expected 0 value argument(s), got 1",
      Case(cons, hd, hd) -> "repeated pattern binder",
      Case(cons, hd, nil(nat)) -> "constructor type arguments",
      Case(cons, hd, ∅) -> "Unsupported pattern"
    )
    val validation = Theorem.generated(k :: list(bool) |- k === k) {
      for (invalid, message) <- cases do
        var entered = false
        rejectWithoutRegistration(message) {
          Induction(k, list.specialize(bool)) {
            invalid subproof {
              entered = true
              have(thesis) by Tautology
            }
          }(thesis)
        }
        assert(!entered)
      have(thesis) by Tautology
    }
    assert(!validation.hasErrorsOrSorry)
