package lisa.hol

import lisa.SetTheoryLibrary
import lisa.hol.Import.Transformers.*
import lisa.hol.VarsAndFunctions.*
import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.BasicStepTactic.*
import org.scalatest.funsuite.AnyFunSuite

class TypeInstantiationScopeSuite extends AnyFunSuite:
  private object Owner extends lisa.HOL:
    val theorem = Theorem(⊤):
      have(⊤) by Restate
  private val a = TypeVariable(K.Identifier("scope-A"))
  private val b = TypeVariable(K.Identifier("scope-B"))
  private val c = TypeVariable(K.Identifier("scope-C"))
  private val observe = variable[Ind >>: Prop](K.Identifier("scope-observe"))

  private def instantiate(statement: Sequent, substitutions: Seq[(Variable[Ind], Expr[Ind])]): Sequent =
    import SetTheoryLibrary.{BaseProof, THMFromProof}
    val proof = new BaseProof(Owner.theorem.asInstanceOf[THMFromProof])
    given proof.type = proof
    // Supply an open premise only to the tactic fixture, never register it as a theorem.
    val premise = proof.newProofStep(proof.ValidProofTactic(
      statement, Seq(K.Restate(statement.underlying, -1)), Seq()
    )(using Restate))
    ExtendedHOLSteps._INST_TYPE_RENAME(substitutions, premise) match
      case valid: proof.ValidProofTactic =>
        val imports = valid.imports.map(proof.sequentOfFact(_).underlying).toIndexedSeq
        val checked = K.SCProof(valid.scps.toIndexedSeq, imports)
        assert(K.SCProofChecker.checkSCProof(checked).isValid)
        assert(imports.contains(statement.underlying))
        valid.bot
      case invalid: proof.InvalidProofTactic => fail(invalid.message)

  private def instantiate(term: Expr[Ind]): Sequent = instantiate(() |- observe(term), Seq(a -> c, b -> c))

  test("preserve nested binder scope when distinct HOL types become equal"):
    val outer = mkTypedVar("y", a)
    val inner = mkTypedVar("y", b)
    val result = instantiate(fun(outer, fun(inner, outer)))
    val x = mkTypedVar("outer", c)
    val y = mkTypedVar("inner", c)
    assert(K.isSameSequent(result.underlying, (() |- observe(fun(x, fun(y, x)))).underlying))

  test("preserve a free variable when its type merges with a same-named binder"):
    val free = mkTypedVar("y", a)
    val bound = mkTypedVar("y", b)
    val result = instantiate(fun(bound, free))
    val x = mkTypedVar("bound", c)
    val y = mkTypedVar("y", c)
    assert(K.isSameSequent(result.underlying, (() |- observe(fun(x, y))).underlying))

  test("retain ordinary shadowing when the bound variables already coincide"):
    val y = mkTypedVar("shadow", a)
    val result = instantiate(fun(y, fun(y, y)))
    val x = mkTypedVar("outer", c)
    val z = mkTypedVar("inner", c)
    assert(K.isSameSequent(result.underlying, (() |- observe(fun(x, fun(z, z)))).underlying))

  test("freshen an unchanged binder when free-variable canonicalization would capture"):
    val free = mkTypedVar("capture", a)
    val bound = mkTypedVar("capture", c)
    val result = instantiate(() |- observe(fun(bound, free)), Seq(a -> c))
    val fresh = mkTypedVar("fresh", c)
    assert(K.isSameSequent(result.underlying, (() |- observe(fun(fresh, bound))).underlying))
    assert(!K.isSameSequent(result.underlying, (() |- observe(fun(bound, bound))).underlying))

  test("canonicalize free variables simultaneously when one target is another source"):
    val ya = mkTypedVar("simultaneous", a)
    val yb = mkTypedVar("simultaneous", b)
    val yc = mkTypedVar("simultaneous", c)
    val result = instantiate(observe(ya) |- observe(yb), Seq(a -> b, b -> c))
    assert(K.isSameSequent(result.underlying, (observe(yb) |- observe(yc)).underlying))

  test("identify free variables whose names and instantiated types coincide"):
    val ya = mkTypedVar("merge", a)
    val yb = mkTypedVar("merge", b)
    val result = instantiate(observe(ya) |- observe(yb), Seq(a -> c, b -> c))
    val y = mkTypedVar("merge", c)
    assert(K.isSameSequent(result.underlying, (observe(y) |- observe(y)).underlying))

  test("preserve free-variable canonicalization in hypotheses as well as conclusions"):
    val y = mkTypedVar("hypothesis", a)
    val result = instantiate(observe(y) |- observe(fun(mkTypedVar("bound", b), y)), Seq(a -> c, b -> c))
    val canonical = mkTypedVar("hypothesis", c)
    val bound = mkTypedVar("bound", c)
    assert(K.isSameSequent(result.underlying, (observe(canonical) |- observe(fun(bound, canonical))).underlying))

  test("match HOL Light INST_TYPE 6156041 from the exported premise and substitution"):
    import lisa.hol.extractor.*
    val input = scala.io.Source.fromResource("inst-type-scope.jsonl")
    val records = try input.getLines().toVector finally input.close()
    given context: ExtractorContext = new ExtractorContext(Iterator.empty, Iterator.empty)
    try
      new Import.StepStore // Register the standard HOL constants used by the fixture.
      val before = upickle.default.read[TheoremStatement](records(0)).sequent.extract.toLisaSequent
      val step = upickle.default.read[ProofLine](records(1)).step.extract.asInstanceOf[lisa.hol.core.INST_TYPE]
      val expected = upickle.default.read[TheoremStatement](records(2)).sequent.extract.toLisaSequent
      val result = instantiate(before, step.insts.toSeq.map((v, t) => v.toLisaVar -> t.toLisaType))
      assert(K.isSameSequent(result.underlying, expected.underlying))
    finally context.close()
