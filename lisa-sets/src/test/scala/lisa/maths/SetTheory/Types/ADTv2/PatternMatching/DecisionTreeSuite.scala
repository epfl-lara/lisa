package lisa.maths.SetTheory.Types.ADTv2.PatternMatching

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Clause
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.DecisionTree
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.DecisionTree.Leaf
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.DecisionTree.Split
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADTv2._
import lisa.maths.SetTheory.Types.ADTv2.interface.ADT
import lisa.maths.SetTheory.Types.ADTv2.interface.Constructor
import lisa.maths.SetTheory.Types.ADTv2.interface.SpecializedADT
import lisa.maths.SetTheory.Types.ADTv2.library.bool
import lisa.maths.SetTheory.Types.ADTv2.library.box
import lisa.maths.SetTheory.Types.ADTv2.library.cons
import lisa.maths.SetTheory.Types.ADTv2.library.fals
import lisa.maths.SetTheory.Types.ADTv2.library.list
import lisa.maths.SetTheory.Types.ADTv2.library.nat
import lisa.maths.SetTheory.Types.ADTv2.library.nil
import lisa.maths.SetTheory.Types.ADTv2.library.pack
import lisa.maths.SetTheory.Types.ADTv2.library.product
import lisa.maths.SetTheory.Types.ADTv2.library.succ
import lisa.maths.SetTheory.Types.ADTv2.library.tru
import lisa.maths.SetTheory.Types.ADTv2.library.void
import lisa.maths.SetTheory.Types.ADTv2.library.zero
import lisa.maths.SetTheory.Types.ADTv2.library.{pair => productPair}
import lisa.utils.prooflib.OutputManager
import org.scalatest.funsuite.AnyFunSuite

/**
 * Checks the typed case analysis and source bindings retained for proof reconstruction.
 */
class DecisionTreeSuite extends AnyFunSuite:
  private given OutputManager = new OutputManager:
    val stringWriter = new java.io.StringWriter
    def finishOutput(exception: Exception): Nothing = throw exception

  private val A, hd, hd2, tl, tl2, xs, x = variable[Ind]

  private def compileTree(domain: SpecializedADT[?], constructor: Constructor[?], cases: Seq[Seq[Expr[Ind]]]): DecisionTree =
    val clauses = cases.map { args =>
      PatternValidation.resolveCase(constructor, args, domain).fold(error => fail(error), pattern => pattern)
    }
    DecisionTree.compile(domain, clauses).fold(error => fail(error), tree => tree)

  private def leaves(tree: DecisionTree): Vector[Leaf] = tree match
    case leaf: Leaf => Vector(leaf)
    case Split(_, _, branches) => branches.flatMap((_, child) => leaves(child))

  test("constructor lookup preserves ownership and specialization without initializing unrelated wrappers"):
    val targetType = nat.term
    val first = adt("constructorIndexFirst", "A", Seq(("empty", Seq.empty), ("pack", Seq(("value", "A")))))
    val other = adt("constructorIndexOther", "A", Seq(("pack", Seq(("value", "A")))))
    val firstId = first.semantic.constructors(1).id
    val otherId = other.semantic.constructors.head.id
    val firstIntro = "constructorIndexFirst/pack/introduction"
    val otherIntro = "constructorIndexOther/pack/introduction"
    assert(lisa.SetTheoryLibrary.theory.getTheorem(firstIntro).isEmpty)
    assert(lisa.SetTheoryLibrary.theory.getTheorem(otherIntro).isEmpty)

    val beforeLookup = lisa.SetTheoryLibrary.last
    assert(ADT.getConstructor(other.id).isEmpty)
    assert(PatternValidation.constructorApplication(other(targetType)).isLeft)
    assert(lisa.SetTheoryLibrary.last == beforeLookup)

    val constructor = ADT.getConstructor(firstId).getOrElse(fail("Registered constructor was not found."))
    assert(constructor.adt eq first)
    assert(constructor eq first.constructors(1))
    assert(lisa.SetTheoryLibrary.theory.getTheorem(firstIntro).isDefined)
    assert(lisa.SetTheoryLibrary.theory.getTheorem(otherIntro).isEmpty)

    val afterLookup = lisa.SetTheoryLibrary.last
    val (decoded, typeArgs, valueArgs) = PatternValidation
      .constructorApplication(constructor(targetType) * x)
      .fold(error => fail(error), identity)
    assert(decoded eq constructor)
    assert(typeArgs == Seq(targetType) && valueArgs == List(x))
    assert(ADT.getConstructor(firstId).exists(_ eq constructor))
    assert(lisa.SetTheoryLibrary.last == afterLookup)
    assert(lisa.SetTheoryLibrary.theory.getTheorem(otherIntro).isEmpty)

    val otherConstructor = ADT.getConstructor(otherId).getOrElse(fail("Second constructor was not found."))
    assert(otherConstructor.adt eq other)
    assert(otherConstructor.id != constructor.id)
    assert(PatternValidation.resolveCase(otherConstructor, Seq(x), first.specialize(targetType)).isLeft)

  test("an empty datatype retains an exhaustive split with no branches"):
    val domain = void.specialize()
    val tree = DecisionTree.compile(domain, Seq.empty).fold(error => fail(error), tree => tree)
    tree match
      case Split(path, actualDomain, branches) =>
        assert(path.isEmpty)
        assert(actualDomain.base.id == void.id)
        assert(actualDomain.typeArgs.isEmpty)
        assert(branches.isEmpty)
      case _ => fail("An empty datatype must retain its empty case analysis.")

  test("reordered clauses retain their source indices and ordered bindings across multiple fields"):
    val domain = product.specialize(list(bool), list(bool))
    val constructor = productPair
    val cases: Seq[Seq[Expr[Ind]]] = Seq(
      Seq(cons(bool) * hd * tl, cons(bool) * hd2 * tl2),
      Seq(nil(bool), nil(bool)),
      Seq(nil(bool), cons(bool) * hd2 * tl2),
      Seq(cons(bool) * hd * tl, nil(bool))
    )
    val language = lisa.SetTheoryLibrary.theory.language().toSet
    val last = lisa.SetTheoryLibrary.last
    val registered = ADT.allADTs.toSet
    val tree = compileTree(domain, constructor, cases)
    assert(
      leaves(tree).sortBy(_.clauseIndex) == Vector(
        Leaf(0, Vector(hd -> List(0, 0), tl -> List(0, 1), hd2 -> List(1, 0), tl2 -> List(1, 1))),
        Leaf(1, Vector.empty),
        Leaf(2, Vector(hd2 -> List(1, 0), tl2 -> List(1, 1))),
        Leaf(3, Vector(hd -> List(0, 0), tl -> List(0, 1)))
      )
    )
    assert(lisa.SetTheoryLibrary.theory.language().toSet == language)
    assert(lisa.SetTheoryLibrary.last == last)
    assert(ADT.allADTs.toSet == registered)

  test("a binder retains its whole subtree when other disjoint clauses inspect that subtree"):
    val domain = product.specialize(list(bool), bool)
    val tree = compileTree(
      domain,
      productPair,
      Seq(
        Seq(xs, tru),
        Seq(nil(bool), fals),
        Seq(cons(bool) * hd * tl, fals)
      )
    )
    val expected = Map(
      0 -> Vector(xs -> List(0)),
      1 -> Vector.empty,
      2 -> Vector(hd -> List(0, 0), tl -> List(0, 1))
    )
    val selected = leaves(tree)
    assert(selected.map(_.clauseIndex).toSet == expected.keySet)
    selected.foreach(leaf => assert(leaf.bindings == expected(leaf.clauseIndex)))

  test("nested splits retain the constructor identity and explicit type arguments at each occurrence"):
    val domain = box.specialize(box(A))
    val tree = compileTree(domain, pack, Seq(Seq(pack(A) * x)))
    tree match
      case Split(rootPath, rootDomain, Vector((outer, Split(innerPath, innerDomain, Vector((inner, leaf: Leaf)))))) =>
        assert(rootPath.isEmpty)
        assert(rootDomain.base.id == box.id)
        assert(rootDomain.typeArgs == Seq(box(A)))
        assert(innerPath == List(0))
        assert(innerDomain.base.id == box.id)
        assert(innerDomain.typeArgs == Seq(A))
        assert(outer.id == pack.id && inner.id == pack.id)
        assert(leaf == Leaf(0, Vector(x -> List(0, 0))))
      case _ => fail("Expected one specialized box split at each of the two constructor occurrences.")

  test("mapping clause bodies shares resolved patterns, decision trees, and body-independent proofs"):
    val domain = nat.specialize()
    val successor = Pattern.fromResolved(PatternValidation.resolveCase(succ, Seq(x), domain).fold(error => fail(error), identity))
    val base = Pattern.fromResolved(PatternValidation.resolveCase(zero, Seq.empty, domain).fold(error => fail(error), identity))
    val system = PatternSystem
      .compile(domain, Seq(Clause(successor, x: Expr[Ind]), Clause(base, zero: Expr[Ind])))
      .fold(error => fail(error), identity)
    val coverage = system.coverage
    val selection = system.branchSelectionSchema(succ.semantic)
    val incompatibility = system.incompatible(successor, base)
    val mapped = system.map(body => succ * body)

    assert(mapped.clauses.map(_.payload) == Seq(succ * x, succ * zero))
    assert(mapped.patterns.zip(system.patterns).forall((left, right) => left eq right))
    assert(mapped.decisionTree eq system.decisionTree)
    assert(mapped.coverage eq coverage)
    assert(mapped.branchSelectionSchema(succ.semantic) eq selection)
    assert(mapped.incompatible(successor, base) eq incompatibility)
    assert(!coverage.withSorry && !selection.withSorry && !incompatibility.withSorry)

  test("branch selection reuses one schema across inputs without capturing type or pattern variables"):
    val parameter = Variable[Ind]("branchInput")
    val domain = list.specialize(parameter)
    val shapes = Seq(
      nil -> Seq.empty[Expr[Ind]],
      cons -> Seq(hd, nil(parameter)),
      cons -> Seq(hd, cons(parameter) * hd2 * tl2)
    )
    val patterns = shapes.map { (constructor, args) =>
      Pattern.fromResolved(PatternValidation.resolveCase(constructor, args, domain).fold(error => fail(error), identity))
    }
    val system = PatternSystem
      .compile(domain, patterns.map(pattern => Clause(pattern, zero: Expr[Ind])))
      .fold(error => fail(error), identity)
    val schema = system.branchSelectionSchema(cons.semantic)
    val schematicInputs = schema.statement.freeTermVars - parameter
    assert(schematicInputs.size == 1)
    val input = schematicInputs.head
    val innerBinder = patterns.last.variables2.last
    val conflictingTerm = cons(parameter) * innerBinder * nil(parameter)
    val checked = Theorem(True) { proof ?=>
      val last = lisa.SetTheoryLibrary.last
      for subject <- Seq(xs, conflictingTerm, input) do
        val instance = system.branchSelectionFor(cons.semantic, subject)
        val statement = proof.getSequent(instance)
        assert(statement.freeTermVars.contains(parameter))
        assert(subject.freeTermVars.subsetOf(statement.freeTermVars))
        have(statement) by Restate.from(instance)
        assert(lisa.SetTheoryLibrary.last == last)
      have(thesis) by Restate
    }
    assert(!checked.withSorry)
    assert(system.map(identity).branchSelectionSchema(cons.semantic) eq schema)
    val foreign = tru.semantic
    val last = lisa.SetTheoryLibrary.last
    intercept[IllegalArgumentException](system.branchSelectionSchema(foreign))
    assert(lisa.SetTheoryLibrary.last == last)

  test("constructor input typing specializes the existing theorem without registering wrappers"):
    val domain = list.specialize(A)
    val pattern = Pattern.fromResolved(PatternValidation.resolveCase(cons, Seq(hd, tl), domain).fold(error => fail(error), identity))
    val introduction = cons.introApp
    val checked = Theorem(True) {
      val last = lisa.SetTheoryLibrary.last
      for head <- Seq(x, A) do
        val instance = pattern.inputTypingAt(Seq(head, xs), list(A))
        have((head :: A, xs :: list(A)) |- cons(A) * head * xs :: list(A)) by Restate.from(instance)
        assert(lisa.SetTheoryLibrary.last == last)
      have(thesis) by Restate
    }
    assert(!introduction.withSorry && !checked.withSorry)

  test("nested recursive agreement points require SelfRef fields throughout their paths"):
    val recursive = Pattern.fromResolved(
      PatternValidation.resolveCase(succ, Seq(succ * x), nat.specialize()).fold(error => fail(error), identity)
    )
    val payload = Pattern.fromResolved(
      PatternValidation.resolveCase(pack, Seq(succ * x), box.specialize(nat)).fold(error => fail(error), identity)
    )
    assert(recursive.recursiveAgreementPoints(nat) == recursive.variables2.drop(recursive.arity))
    assert(recursive.recursiveAgreementPoints(nat).size == 1)
    assert(payload.recursiveAgreementPoints(nat).isEmpty)
