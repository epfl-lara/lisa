package lisa.automation.superposition

import lisa.automation.{ProofSyntax => K}
import org.scalatest.funsuite.AnyFunSuite
import sctptp.Parser
import sctptp.{SequentCalculus => SC}

import java.nio.file.Files

object SctptpTest extends org.scalatest.Assertions:
  def checked(certificate: K.ProofCertificate): SC.SCProof[?] =
    val proof = Sctptp.fromKernel(certificate).fold(fail(_), identity)
    assert(SC.checkProof(proof) == SC.StepCheckOK)
    val file = Files.createTempFile("lisa-sctptp", ".p")
    try
      Files.writeString(file, SC.ProofToString(proof))
      val parsed = Parser.reconstructProof(file.toFile)
      assert(parsed.steps == proof.steps)
      assert(SC.checkProof(parsed) == SC.StepCheckOK)
    finally Files.delete(file)
    proof

class SctptpTest extends AnyFunSuite:
  import SctptpTest.checked
  import K.*

  private val p = Constant(Identifier("p"), Prop)
  private val q = Constant(Identifier("q"), Prop)
  private val r = Constant(Identifier("r"), Prop)
  private val pred = Constant(Identifier("pred"), Ind -> Prop)
  private val a = Constant(Identifier("a"), Ind)
  private val b = Constant(Identifier("b"), Ind)
  private val x = Variable(Identifier("x"), Ind)
  private val y = Variable(Identifier("y"), Ind)

  private def cert(step: CertificateStep, imports: Sequent*) = ProofCertificate(Vector(step), imports.toVector)

  test("weakening adds one formula per step on its original side and can reuse an earlier import") {
    val start = p |- q
    val goal = (p, q, r) |- (q, r)
    val proof = checked(cert(Weakening(goal, -1), start))
    assert(proof.steps.count(_.isInstanceOf[SC.LeftWeaken]) == 2)
    assert(proof.steps.count(_.isInstanceOf[SC.RightWeaken]) == 1)
    val reused = checked(ProofCertificate(Vector(Hypothesis(q |- q, q), Weakening(start, -1)), Vector(start)))
    assert(reused.conclusion == proof.steps.head.bot)
  }

  test("weakening rejects equivalent replacements, removal, and side changes") {
    val conjunction = and(p)(q)
    val start = conjunction |- r
    for goal <- Seq(and(q)(p) |- (p, r), (p, q) |- r, () |- (r, conjunction), conjunction |- ()) do
      val error = Sctptp.fromKernel(cert(Weakening(goal, -1), start)).left.toOption.get
      assert(error.contains("step 0 (Weakening)"))
      assert(error.contains("original side"))
  }

  test("rejects Restate even on identical sequents and at subproof import boundaries") {
    val s = p |- p
    val identity = cert(Restate(s, -1), s)
    assert(Sctptp.fromKernel(identity).left.toOption.get.contains("step 0 (Restate)"))
    val outer = p |- and(p)(p)
    val inner = cert(Weakening(s, -1), s)
    assert(Sctptp.fromKernel(cert(Subproof(inner, Seq(-1)), outer)).left.toOption.get.contains("Restate"))
    checked(cert(Subproof(inner, Seq(-1)), s))
  }

  test("rejects a higher-order symbol, a missing cut pivot, and an unsupported proof rule") {
    val higher = Constant(Identifier("holds"), Prop -> Prop)
    val s = higher(p) |- higher(p)
    assert(Sctptp.fromKernel(cert(Hypothesis(s, higher(p)))).left.toOption.get.contains("first-order"))
    assert(Sctptp.fromKernel(cert(Cut(() |- (), -1, -2, p), () |- q, q |- ())).isLeft)
    assert(Sctptp.fromKernel(cert(Sorry(() |- p))).isLeft)
  }

  test("strict propositional rules retain their rule names and principal indices") {
    val conjunction = and(p)(q)
    val disjunction = or(p)(q)
    val implication = implies(p)(q)
    val converse = implies(q)(p)
    val biconditional = iff(p)(q)
    val cases = Seq(
      cert(LeftAnd(conjunction |- (), -1, p, q), (p, q) |- ()),
      cert(LeftImplies(implication |- (), -1, -2, p, q), () |- p, q |- ()),
      cert(LeftIff(biconditional |- (), -1, p, q), (implication, converse) |- ()),
      cert(LeftNot(neg(p) |- (), -1, p), () |- p),
      cert(RightNot(() |- neg(p), -1, p), p |- ()),
      cert(RightOr(() |- disjunction, -1, p, q), () |- (p, q)),
      cert(RightImplies(() |- implication, -1, p, q), p |- q),
      cert(RightIff(() |- biconditional, -1, -2, p, q), () |- implication, () |- converse),
      cert(LeftOr(or(disjunction)(r) |- (), Seq(-1, -2, -3), Seq(p, q, r)), p |- (), q |- (), r |- ()),
      cert(RightAnd(() |- and(conjunction)(r), Seq(-1, -2, -3), Seq(p, q, r)), () |- p, () |- q, () |- r)
    )
    cases.foreach(checked)
  }

  test("LeftAnd and RightOr insert exactly the missing operands on the appropriate side") {
    for present <- Seq(Set.empty[Expression], Set[Expression](p), Set[Expression](q), Set[Expression](p, q)) do
      val left = checked(cert(LeftAnd(and(p)(q) |- r, -1, p, q), present |- r))
      val right = checked(cert(RightOr(r |- or(p)(q), -1, p, q), r |- present))
      val missing = 2 - present.size
      assert(left.steps.count(_.isInstanceOf[SC.LeftWeaken]) == missing)
      assert(right.steps.count(_.isInstanceOf[SC.RightWeaken]) == missing)
      assert(left.steps.size == 2 + missing && left.steps.last.isInstanceOf[SC.LeftAnd])
      assert(right.steps.size == 2 + missing && right.steps.last.isInstanceOf[SC.RightOr])

    val repeated = checked(cert(LeftAnd(and(p)(p) |- r, -1, p, p), () |- r))
    assert(repeated.steps.count(_.isInstanceOf[SC.LeftWeaken]) == 1)
    val px = forall(x, pred(x))
    val py = forall(y, pred(y))
    val renamed = checked(cert(RightOr(r |- or(px)(q), -1, px, q), r |- (py, q)))
    assert(renamed.steps.size == 2)
  }

  test("supplying a missing operand preserves the other formulas in the premise") {
    assert(Sctptp.fromKernel(cert(LeftAnd(and(p)(q) |- r, -1, p, q), (p, r) |- r)).isLeft)
    assert(Sctptp.fromKernel(cert(RightOr(r |- or(p)(q), -1, p, q), r |- (p, r))).isLeft)
  }

  test("quantifier and epsilon steps round-trip with witnesses and eigenvariables") {
    val body = pred(x)
    val all = forall(Lambda(x, body))
    val some = exists(Lambda(x, body))
    checked(cert(LeftForall(all |- (), -1, body, x, a), pred(a) |- ()))
    checked(cert(LeftExists(some |- (), -1, body, x), body |- ()))
    checked(cert(RightForall(() |- all, -1, body, x), () |- body))
    checked(cert(RightExists(() |- some, -1, body, x, a), () |- pred(a)))
    checked(cert(RightEpsilon(() |- pred(epsilon(Lambda(x, body))), -1, body, x, a), () |- pred(a)))
  }

  test("simultaneous schema instantiation handles swaps, nested applications, and predicate parameters") {
    val f = Variable(Identifier("f"), Ind -> Ind)
    val g = Constant(Identifier("g"), Ind -> Ind)
    val schematic = Variable(Identifier("p"), Ind -> Prop)
    val original = schematic(f(f(x))) |- pred(y)
    val expected = neg(pred(g(g(y)))) |- pred(x)
    checked(cert(InstSchema(expected, -1, Map(x -> y, y -> x, f -> g, schematic -> Lambda(x, neg(pred(x))))), original))
  }

  test("simultaneous rewriting keeps holes distinct from the replacement terms and cuts comparison proofs") {
    val relation = Constant(Identifier("rel"), Ind -> (Ind -> Prop))
    val goal = (equality(x)(y), equality(y)(x)) |- relation(y)(x)
    val replacements = Seq((x, y), (y, x))
    checked(cert(RightSubstEq(goal, -1, replacements, (Seq(x, y), relation(x)(y))), () |- relation(x)(y)))
    checked(cert(LeftSubst(pred(b) |- (), -1, Seq(-2), Seq((a, b, Nil)), (Seq(x), pred(x))), pred(a) |- (), () |- equality(a)(b)))
    val hole = Variable(Identifier("a"), Prop)
    checked(cert(RightSubstEq(iff(p)(q) |- neg(q), -1, Seq(p -> q), (Seq(hole), neg(hole))), () |- neg(p)))
  }

  test("schema instantiation under epsilon avoids capture") {
    val schematic = Variable(Identifier("p"), Ind -> Prop)
    val relation = Constant(Identifier("rel"), Ind -> (Ind -> Prop))
    val original = pred(epsilon(Lambda(x, schematic(x))))
    val expected = pred(epsilon(Lambda(y, relation(x)(y))))
    checked(cert(InstSchema(() |- expected, -1, Map(schematic -> Lambda(y, relation(x)(y)))), () |- original))
  }

  test("indexed symbols and literal identifier suffixes stay distinct") {
    val symbols = Seq(Identifier("sk", 1), Identifier("sk_1"), Identifier("sk_n1"), Identifier("Sk"), Identifier("lisaCSk"))
    val atoms = symbols.map(id => pred(Constant(id, Ind)))
    val proof = checked(cert(Hypothesis(Sequent(atoms.toSet, Set(atoms.last)), atoms.last)))
    assert(proof.conclusion.left.distinct.size == atoms.size)
  }

  test("binary rules preserve the side context of each premise") {
    val both = cert(LeftOr(or(p)(q) |- (), Seq(-1, -1), Seq(p, q)), (p, q) |- ())
    val converse = cert(LeftImplies(implies(p)(q) |- (), -1, -1, p, q), q |- p)
    assert(Sctptp.fromKernel(both).isLeft)
    assert(Sctptp.fromKernel(converse).isLeft)
  }

  test("cut permits a renamed bound variable but weakening preserves the original binder") {
    val px = forall(Lambda(x, pred(x)))
    val py = forall(Lambda(y, pred(y)))
    checked(cert(Cut(() |- (), -1, -2, px), () |- px, py |- ()))
    assert(Sctptp.fromKernel(cert(Weakening(py |- (), -1), px |- ())).isLeft)
  }

  test("schema instantiation normalizes applied first-order templates and checks even discarded arguments") {
    val rel = Variable(Identifier("r"), Ind -> (Ind -> Prop))
    val fun = Variable(Identifier("f"), Ind -> Ind)
    val image = Lambda(x, Lambda(y, and(pred(x))(pred(y))))
    val argument = Lambda(x, b)
    val premise = () |- rel(fun(a))(a)
    val goal = () |- image(argument(a))(a)
    checked(cert(InstSchema(goal, -1, Map(rel -> image, fun -> argument)), premise))

    val higher = Constant(Identifier("select"), (Ind -> Prop) -> Ind)
    val discarded = Lambda(x, p)(higher(pred))
    assert(Sctptp.fromKernel(cert(Hypothesis(discarded |- discarded, discarded))).isLeft)
  }

  test("clause import composition prefers an identical import and restates a changed presentation") {
    val working = p |- q
    val different = () |- (neg(p), q)
    val base = cert(Weakening(working, -1), working)
    for originals <- Seq(Vector(different, working), Vector(working, different)) do
      val proof = Clausal.composeProof(base, originals)
      assert(proof.steps == Vector(Subproof(base, Seq(-(originals.indexOf(working) + 1)))))
      checked(proof)
    val adapted = Clausal.composeProof(base, Vector(different))
    assert(adapted.steps == Vector(Restate(working, -1), Subproof(base, Seq(0))))
  }
