package lisa.hol

import lisa.SetTheoryLibrary
import lisa.hol.HOLHelperTheorems.{One, 𝔹}
import lisa.hol.VarsAndFunctions.*
import lisa.hol.basics.Connectives.{hand, himp, hnot}
import lisa.hol.basics.Disjunction.hor
import lisa.hol.basics.Exists.hexists
import lisa.hol.basics.Forall.hforall
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Types.TypingHelpers.{fun as _, *, given}
import lisa.utils.K
import lisa.utils.fol.FOL.{*, given}
import lisa.utils.prooflib.*
import lisa.utils.prooflib.ProofHelpers.*
import org.scalatest.funsuite.AnyFunSuite

class FromHOLSuite extends AnyFunSuite:
  private given Library = SetTheoryLibrary
  private val A = typevar
  private val p, q = typedvar(𝔹)
  private val x, y = typedvar(A)
  private val P = typedvar(A ->: 𝔹)

  private def premise(term: Expr[Ind], hypotheses: Set[Expr[Ind]] = Set.empty): Thm =
    val encoded = HOLSequent(hypotheses, term)
    val statement = encoded ++<< (getContext(encoded) |- ())
    val kernel = lisa.kernel.proof.Assume(using SetTheoryLibrary.theory)(statement.underlying).toOption.get
    Thm(statement, kernel)

  private def check(result: ProofJudgement, expected: Sequent, source: Thm): Thm =
    assert(result.isValid, result.errors.map(_.message).mkString("\n"))
    assert(!result.kernel.usesSorry)
    assert(result.kernel.assumptions == source.kernel.assumptions)
    assert(isSameSequent(result.thm.statement, expected), s"${result.thm.statement}\nExpected: $expected")
    result.thm

  test("translate connectives inside out and rewrite hypotheses too"):
    val term = himp * (hand * p * q) * (hnot * q)
    val source = premise(term, Set(hand * p * q))
    val expected = (getContext(source.statement) + (eqOne(p) /\ eqOne(q))) |- ((eqOne(p) /\ eqOne(q)) ==> !eqOne(q))
    check(FromHOL.fromHOL(source), expected, source)

  test("translate equality without descending into higher-order term arguments"):
    val source = premise(x =:= y)
    check(FromHOL.fromHOL(source), getContext(source.statement) |- (x === y), source)
    val consumer = typedvar(𝔹 ->: 𝔹)
    val opaque = premise(consumer * (hand * p * q))
    check(FromHOL.fromHOL(opaque), opaque.statement, opaque)

  test("translate Boolean equality as equivalence recursively"):
    val source = premise((hand * p * q) =:= (hnot * p))
    check(FromHOL.fromHOL(source), getContext(source.statement) |- ((eqOne(p) /\ eqOne(q)) <=> !eqOne(p)), source)

  test("translate HOL disjunction with its checked correctness theorem"):
    assert(lisa.hol.basics.Disjunction.horCorrect.errors.isEmpty)
    val source = premise(hor * p * (hnot * q))
    check(FromHOL.fromHOL(source), getContext(source.statement) |- (eqOne(p) \/ !eqOne(q)), source)
    assert(HOLPrinting.boolean(hor * p * q).contains(" ∨ "))

  test("translate nested typed quantifiers and discharge bound-variable typings"):
    val term = hforall(A) * fun(x, hexists(A) * fun(y, hand * (x =:= y) * (hnot * (x =:= y))))
    val source = premise(term)
    val target = ∀(x, (x ∈ A) ==> ∃(y, (y ∈ A) /\ (x === y) /\ !(x === y)))
    val result = check(FromHOL.fromHOL(source), getContext(source.statement) |- target, source)
    assert(result.left.forall(_.freeVars.forall(variable => variable != x && variable != y)))

  test("translate a quantifier over a predicate without a lambda"):
    val source = premise(hforall(A) * P)
    check(FromHOL.fromHOL(source), getContext(source.statement) |- ∀(x, (x ∈ A) ==> eqOne(P * x)), source)

  test("translate nontrivial quantified bodies and both truth constants"):
    val source = premise(hforall(A) * fun(x, hexists(A) * fun(y, hand * (P * x) * (x =:= y))))
    val target = ∀(x, (x ∈ A) ==> ∃(y, (y ∈ A) /\ eqOne(P * x) /\ (x === y)))
    check(FromHOL.fromHOL(source), getContext(source.statement) |- target, source)
    for term <- Seq(One, lisa.hol.basics.Truth.holT) do
      val source = premise(term)
      check(FromHOL.fromHOL(source), source.left |- ⊤, source)
    for term <- Seq(HOLHelperTheorems.Zero, lisa.hol.basics.False.holF) do
      val source = premise(term)
      check(FromHOL.fromHOL(source), source.left |- ⊥, source)

  test("keep a free variable distinct from a shadowing binder"):
    val quantified = hforall(A) * fun(x, x =:= x)
    val source = premise(quantified, Set(P * x))
    val target = (getContext(source.statement) + eqOne(P * x)) |- ∀(y, (y ∈ A) ==> (y === y))
    check(FromHOL.fromHOL(source), target, source)

  test("return judgements directly or through a named store"):
    val source = premise(hand * p * q)
    val target = getContext(source.statement) |- (eqOne(p) /\ eqOne(q))
    val store = Map("AND" -> source)
    val result = FromHOL.fromHOL(source)
    check(result, target, source)
    check(FromHOL.fromHOL("AND", store.apply), target, source)
    assert(!BasicStep.Weakening(getContext(source.statement) |- !eqOne(p), result.kernel).isValid)
    intercept[NoSuchElementException](FromHOL.fromHOL("missing", store.apply))

  test("print native notation without altering the encoded sequent"):
    val term = hforall(A) * fun(x, hand * (x =:= x) * (hnot * p))
    val source = premise(term)
    val displayed = HOLPrinting.displayed(source.statement)
    assert(displayed.underlying == source.statement.underlying)
    val text = displayed.toString
    assert(text.contains("∀("), text)
    assert(text.contains(" ∧ "), text)
    assert(text.contains("¬("), text)
    assert(!text.contains("hforall") && !text.contains("hand") && !text.contains("hnot"), text)
    val indexed = TypedVariable(K.Identifier("x", 3), A)
    assert(HOLPrinting.boolean(hforall(A) * fun(indexed, indexed =:= x)).contains(indexed.id.toString))
    val unrelated = Constant[Ind](K.Identifier("unrelated.hand"))
    assert(!HOLPrinting.boolean(unrelated * p * q).contains(" ∧ "))

  test("HOLTheorem delegates its displayed statement and retains a checked proof"):
    val output = new StringOutputManager
    object Example extends lisa.HOL:
      val identity = HOLTheorem(using output, sourcecode.FullName("FromHOLSuite.identity"), sourcecode.Name("identity"), summon[sourcecode.Line], summon[sourcecode.File])(
        eqOne(hand * p * q) |- eqOne(hand * p * q)
      ):
        have(thesis) by Hypothesis
      private val native = eqOne(p) /\ eqOne(q)
      private val goal = (p ∈ 𝔹, q ∈ 𝔹, native) |- native
      val translated = fromHOL(identity)
      val direct = Theorem(goal):
        have(translated)
      val named = Theorem(goal):
        val res = fromHOL("identity", Map("identity" -> identity.thm))
        have(res)
    assert(Example.identity.errors.isEmpty)
    assert(!Example.identity.thm.kernel.usesSorry)
    assert(Example.direct.errors.isEmpty)
    assert(Example.named.errors.isEmpty)
    assert(!Example.direct.kernel.usesSorry && !Example.named.kernel.usesSorry)
    assert(output.toString.contains(" ∧ "), output.toString)
    assert(!output.toString.contains("hand("), output.toString)

/** Exercise real imported statements without keeping exported traces in the test suite. */
object FromHOLImportCheck extends lisa.HOL:
  override def main(args: Array[String]): Unit =
    require(args.length == 1, "FromHOLImportCheck <export-prefix>")
    val imported = Import.importFromPrefix(args(0), 50, failFast = true)
    val store: String => Thm = name => lisa.SetTheoryLibrary.theorems.get(s"Import.$name").get.thm
    val examples = Set("EQ_SYM", "CONJ_ASSOC", "DISJ_ASSOC", "IMP_CONJ", "FORALL_SIMP", "EXISTS_SIMP", "FORALL_AND_THM")
    for timing <- imported do
      val name = timing.theorem.name
      val result = FromHOL.fromHOL(store(name))
      require(result.isValid, s"$name: ${result.errors.map(_.message).mkString("; ")}")
      require(!result.kernel.usesSorry, s"$name: translation uses Sorry")
      require(result.kernel.assumptions == store(name).kernel.assumptions, s"$name: translation introduced a proof hole")
      if examples.contains(name) then println(s"FIRST_ORDER $name: ${result.thm.statement}")
    println(s"FIRST_ORDER checked ${imported.size} translations")
