package lisa.kernel

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker._
import lisa.kernel.proof.SCProofCheckerJudgement._
import lisa.kernel.proof.SequentCalculus._
import org.scalactic.source.Position
import org.scalatest.funsuite.AnyFunSuite

class SCProofCheckerSuite extends AnyFunSuite {

  def singleStepTest(failing: Boolean)(
      name: String,
      premises: Seq[Sequent],
      step: SCProofStep
  )(implicit
      pos: Position
  ) // take the position from the call site
      : Unit = {
    // the premises are the entire proof context
    val references = premises.apply(_)

    test(name) {
      val judgement =
        checkSingleSCStep(
          premises.length,
          step,
          references,
          0 // no imports
        )
      judgement match {
        case SCValidProof(_, _) =>
          if (failing) fail(s"Expected the proof step to be invalid, but it was valid.")
          else ()
        case SCInvalidProof(_, _, message) =>
          if (!failing) fail(s"Expected the proof step to be valid, but it was invalid, with message: $message")
          else ()
      }
    }(using pos)
  }

  def posTest(
      name: String,
      premises: Seq[Sequent],
      step: SCProofStep
  )(implicit pos: Position): Unit =
    singleStepTest(failing = false)(name, premises, step)(using pos)

  def negTest(
      name: String,
      premises: Seq[Sequent],
      step: SCProofStep
  )(implicit pos: Position): Unit =
    singleStepTest(failing = true)(name, premises, step)(using pos)

  // ## all steps to check

  // ## case Restate(s, t1) =>

  val restateTests = {
    val (p, q, r, s) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop),
      Constant(Identifier("r"), Prop),
      Constant(Identifier("s"), Prop)
    )
    val empty = Set.empty[Expression]

    val positivePairs = Seq(
      (
        Sequent(Set(p), Set(p)),
        Sequent(Set(p), Set(p))
      ),
      (
        Sequent(Set(and(p)(q)), Set(r)),
        Sequent(Set(and(q)(p)), Set(r))
      ),
      (
        Sequent(Set(p), Set(or(q)(r))),
        Sequent(Set(p), Set(or(r)(q)))
      ),
      (
        Sequent(Set(and(and(p)(q))(r)), Set(s)),
        Sequent(Set(and(p)(and(q)(r))), Set(s))
      ),
      (
        Sequent(Set(p), Set(or(or(q)(r))(s))),
        Sequent(Set(p), Set(or(q)(or(r)(s))))
      ),
      (
        Sequent(Set(neg(neg(p))), Set(q)),
        Sequent(Set(p), Set(q))
      ),
      (
        Sequent(Set(p), Set(q, r)),
        Sequent(Set(p, neg(r)), Set(q))
      ),
      (
        Sequent(Set(p, q), Set(r)),
        Sequent(Set(p), Set(r, neg(q)))
      ),
      (
        Sequent(Set(and(p)(q)), Set(r)),
        Sequent(Set(neg(or(neg(p))(neg(q)))), Set(r))
      ),
      (
        Sequent(Set(p), Set(q)),
        Sequent(Set(neg(q)), Set(neg(p)))
      )
    )
    val negativePairs = Seq(
      (
        Sequent(Set(p), Set(q)),
        Sequent(Set(q), Set(p))
      ),
      (
        Sequent(Set(p), Set(q)),
        Sequent(Set(p, r), Set(q))
      ),
      (
        Sequent(Set(p), Set(q)),
        Sequent(Set(p), Set(q, r))
      ),
      (
        Sequent(Set(p), Set(q, r)),
        Sequent(Set(p, r), Set(q))
      ),
      (
        Sequent(Set(p, q), Set(r)),
        Sequent(Set(p), Set(r, q))
      ),
      (
        Sequent(Set(and(p)(q)), Set(r)),
        Sequent(Set(or(p)(q)), Set(r))
      ),
      (
        Sequent(Set(p), Set(or(q)(r))),
        Sequent(Set(p), Set(and(q)(r)))
      ),
      (
        Sequent(Set(p), Set(q)),
        Sequent(Set(neg(q)), Set(p))
      ),
      (
        Sequent(empty, Set(top)),
        Sequent(empty, Set(p))
      )
    )

    for (((prem, bot), i) <- positivePairs.zipWithIndex) {
      posTest(
        name = s"Restate: positive pair #${i + 1}",
        premises = Seq(prem),
        step = Restate(bot, 0)
      )
    }
    for (((prem, bot), i) <- negativePairs.zipWithIndex) {
      negTest(
        name = s"Restate: negative pair #${i + 1}",
        premises = Seq(prem),
        step = Restate(bot, 0)
      )
    }
  }

  // ## case RestateTrue(s) =>

  val restateTrueTests = {
    val (p, q, r) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop),
      Constant(Identifier("r"), Prop)
    )
    val positiveSequents = Seq(
      Sequent(Set.empty, Set(top)),
      Sequent(Set(p), Set(p)),
      Sequent(Set(and(p)(q)), Set(and(q)(p))),
      Sequent(Set(p), Set(or(q)(neg(q)))),
      Sequent(Set(neg(neg(p))), Set(p))
    )
    val negativeSequents = Seq(
      Sequent(Set.empty, Set(p)),
      Sequent(Set(p), Set(q)),
      Sequent(Set(p), Set.empty),
      Sequent(Set.empty, Set(bot)),
      Sequent(Set(and(p)(q)), Set(r))
    )

    for ((bot, i) <- positiveSequents.zipWithIndex) {
      posTest(
        name = s"RestateTrue: positive case #${i + 1}",
        premises = Seq.empty,
        step = RestateTrue(bot)
      )
    }
    for ((bot, i) <- negativeSequents.zipWithIndex) {
      negTest(
        name = s"RestateTrue: negative case #${i + 1}",
        premises = Seq.empty,
        step = RestateTrue(bot)
      )
    }
  }

  // ## case Hypothesis(Sequent(left, right), phi) =>

  val hypothesisTests = {
    val (p, q, r) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop),
      Constant(Identifier("r"), Prop)
    )
    val c = Constant(Identifier("c"), Ind)

    val positiveCases = Seq(
      (Sequent(Set(p), Set(p)), p),
      (Sequent(Set(and(p)(q)), Set(and(q)(p))), and(p)(q)),
      (Sequent(Set(neg(neg(p))), Set(p)), p),
      (Sequent(Set(p, q), Set(r, p)), p),
      (Sequent(Set(neg(or(neg(p))(neg(q)))), Set(and(p)(q))), and(p)(q))
    )
    val negativeCases = Seq(
      (Sequent(Set(p), Set(q)), p),
      (Sequent(Set(q), Set(p)), p),
      (Sequent(Set(q), Set(r)), p),
      (Sequent(Set(neg(q)), Set(p)), q),
      (Sequent(Set.empty, Set.empty), c)
    )

    for (((bot, phi), i) <- positiveCases.zipWithIndex) {
      posTest(
        name = s"Hypothesis: positive case #${i + 1}",
        premises = Seq.empty,
        step = Hypothesis(bot, phi)
      )
    }
    for (((bot, phi), i) <- negativeCases.zipWithIndex) {
      negTest(
        name = s"Hypothesis: negative case #${i + 1}",
        premises = Seq.empty,
        step = Hypothesis(bot, phi)
      )
    }
  }

  // ## case Cut(b, t1, t2, phi) =>

  val cutTests = {
    val (p, q, r, s) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop),
      Constant(Identifier("r"), Prop),
      Constant(Identifier("s"), Prop)
    )
    val c = Constant(Identifier("c"), Ind)

    val positiveCases = Seq(
      (
        Seq(
          Sequent(Set(p), Set(q)),
          Sequent(Set(q), Set(r))
        ),
        Cut(Sequent(Set(p), Set(r)), 0, 1, q)
      ),
      (
        Seq(
          Sequent(Set(p), Set(q)),
          Sequent(Set(r), Set(s))
        ),
        Cut(Sequent(Set(p, r), Set(s)), 0, 1, q)
      ),
      (
        Seq(
          Sequent(Set(p, r), Set(q, s)),
          Sequent(Set(q, s), Set(r))
        ),
        Cut(Sequent(Set(p, r, s), Set(r, s)), 0, 1, q)
      ),
      (
        Seq(
          Sequent(Set(p), Set(and(q)(r))),
          Sequent(Set(and(q)(r), s), Set(q))
        ),
        Cut(Sequent(Set(p, s), Set(q)), 0, 1, and(q)(r))
      )
    )
    val negativeCases = Seq(
      (
        Seq(
          Sequent(Set(p), Set(q)),
          Sequent(Set(q), Set(r))
        ),
        Cut(Sequent(Set(p), Set(r)), 0, 1, p)
      ),
      (
        Seq(
          Sequent(Set(p), Set(q)),
          Sequent(Set(q), Set(r))
        ),
        Cut(Sequent(Set.empty, Set(r)), 0, 1, q)
      ),
      (
        Seq(
          Sequent(Set(p), Set(q)),
          Sequent(Set(q), Set(r))
        ),
        Cut(Sequent(Set(p), Set.empty), 0, 1, q)
      ),
      (
        Seq(
          Sequent(Set(p), Set(q)),
          Sequent(Set(q), Set(r))
        ),
        Cut(Sequent(Set(p), Set(r)), 0, 1, c)
      )
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) {
      posTest(
        name = s"Cut: positive case #${i + 1}",
        premises = premises,
        step = step
      )
    }
    for (((premises, step), i) <- negativeCases.zipWithIndex) {
      negTest(
        name = s"Cut: negative case #${i + 1}",
        premises = premises,
        step = step
      )
    }
  }

  // ## case LeftAnd(b, t1, phi, psi) =>

  val leftAndTests = {
    val (p, q, r, s) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop),
      Constant(Identifier("r"), Prop),
      Constant(Identifier("s"), Prop)
    )
    val c = Constant(Identifier("c"), Ind)

    val positiveCases = Seq(
      (Seq(Sequent(Set(p), Set(r))), LeftAnd(Sequent(Set(and(p)(q)), Set(r)), 0, p, q)),
      (Seq(Sequent(Set(p, q, s), Set(r))), LeftAnd(Sequent(Set(and(p)(q), s), Set(r)), 0, p, q)),
      (Seq(Sequent(Set(and(q)(p)), Set(r))), LeftAnd(Sequent(Set(and(and(p)(q))(s)), Set(r)), 0, and(p)(q), s))
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(p), Set(r))), LeftAnd(Sequent(Set(and(p)(q)), Set.empty), 0, p, q)),
      (Seq(Sequent(Set(p), Set(r))), LeftAnd(Sequent(Set(or(p)(q)), Set(r)), 0, p, q)),
      (Seq(Sequent(Set(p), Set(r))), LeftAnd(Sequent(Set(and(p)(q)), Set(r)), 0, c, q)),
      (Seq(Sequent(Set(p), Set(and(q)(r)))), LeftAnd(Sequent(Set(and(p)(q)), Set(and(r)(q))), 0, p, q))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"LeftAnd: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"LeftAnd: negative case #${i + 1}", premises, step)
  }

  // ## case LeftOr(b, t, disjuncts) =>

  val leftOrTests = {
    val (p, q, r, s) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop),
      Constant(Identifier("r"), Prop),
      Constant(Identifier("s"), Prop)
    )
    val c = Constant(Identifier("c"), Ind)

    val positiveCases = Seq(
      (
        Seq(Sequent(Set(p), Set(r)), Sequent(Set(q), Set(s))),
        LeftOr(Sequent(Set(or(p)(q)), Set(r, s)), Seq(0, 1), Seq(p, q))
      ),
      (
        Seq(Sequent(Set(and(q)(p)), Set(r)), Sequent(Set(s), Set(r))),
        LeftOr(Sequent(Set(or(and(p)(q))(s)), Set(r)), Seq(0, 1), Seq(and(p)(q), s))
      )
    )
    val negativeCases = Seq(
      (Seq.empty, LeftOr(Sequent(Set(or(p)(q)), Set(r)), Seq.empty, Seq.empty)),
      (Seq(Sequent(Set(p), Set(r))), LeftOr(Sequent(Set(or(p)(q)), Set(r)), Seq(0), Seq(p, q))),
      (Seq(Sequent(Set(p), Set(r))), LeftOr(Sequent(Set(or(p)(q)), Set(r)), Seq(0), Seq(c))),
      (Seq(Sequent(Set(p), Set(r)), Sequent(Set(q), Set(s))), LeftOr(Sequent(Set(or(p)(q)), Set(r)), Seq(0, 1), Seq(p, q))),
      (Seq(Sequent(Set(p), Set(r)), Sequent(Set(q), Set(s))), LeftOr(Sequent(Set(and(p)(q)), Set(r, s)), Seq(0, 1), Seq(p, q)))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"LeftOr: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"LeftOr: negative case #${i + 1}", premises, step)
  }

  // ## case LeftImplies(b, t1, t2, phi, psi) =>

  val leftImpliesTests = {
    val (p, q, r, s) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop),
      Constant(Identifier("r"), Prop),
      Constant(Identifier("s"), Prop)
    )
    val c = Constant(Identifier("c"), Ind)

    val positiveCases = Seq(
      (
        Seq(Sequent(Set(r), Set(p, s)), Sequent(Set(q), Set(s))),
        LeftImplies(Sequent(Set(r, implies(p)(q)), Set(s)), 0, 1, p, q)
      ),
      (
        Seq(Sequent(Set(r), Set(and(q)(p))), Sequent(Set(s, neg(neg(q))), Set(r))),
        LeftImplies(Sequent(Set(r, s, implies(and(p)(q))(q)), Set(r)), 0, 1, and(p)(q), q)
      )
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(r), Set(p)), Sequent(Set(q), Set(s))), LeftImplies(Sequent(Set(implies(p)(q)), Set(s)), 0, 1, p, q)),
      (Seq(Sequent(Set(r), Set(p)), Sequent(Set(q), Set(s))), LeftImplies(Sequent(Set(r, implies(p)(q)), Set.empty), 0, 1, p, q)),
      (Seq(Sequent(Set(r), Set(p)), Sequent(Set(q), Set(s))), LeftImplies(Sequent(Set(r, implies(q)(p)), Set(s)), 0, 1, p, q)),
      (Seq(Sequent(Set(r), Set(p)), Sequent(Set(q), Set(s))), LeftImplies(Sequent(Set(r, implies(p)(q)), Set(s)), 0, 1, c, q))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"LeftImplies: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"LeftImplies: negative case #${i + 1}", premises, step)
  }

  // ## case LeftIff(b, t1, phi, psi) =>

  val leftIffTests = {
    val (p, q, r) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop),
      Constant(Identifier("r"), Prop)
    )
    val c = Constant(Identifier("c"), Ind)

    val positiveCases = Seq(
      (Seq(Sequent(Set(implies(p)(q)), Set(r))), LeftIff(Sequent(Set(iff(p)(q)), Set(r)), 0, p, q)),
      (Seq(Sequent(Set(implies(q)(p), implies(p)(q)), Set(r))), LeftIff(Sequent(Set(iff(p)(q)), Set(r)), 0, p, q)),
      (Seq(Sequent(Set(or(neg(p))(q)), Set(r))), LeftIff(Sequent(Set(iff(p)(q)), Set(r)), 0, p, q))
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(implies(p)(q)), Set(r))), LeftIff(Sequent(Set(iff(p)(q)), Set.empty), 0, p, q)),
      (Seq(Sequent(Set(p), Set(r))), LeftIff(Sequent(Set(iff(p)(q)), Set(r)), 0, p, q)),
      (Seq(Sequent(Set(implies(p)(q)), Set(r))), LeftIff(Sequent(Set(iff(p)(r)), Set(r)), 0, p, q)),
      (Seq(Sequent(Set(implies(p)(q)), Set(r))), LeftIff(Sequent(Set(iff(p)(q)), Set(r)), 0, c, q))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"LeftIff: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"LeftIff: negative case #${i + 1}", premises, step)
  }

  // ## case LeftNot(b, t1, phi) =>

  val leftNotTests = {
    val (p, q, r) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop),
      Constant(Identifier("r"), Prop)
    )
    val c = Constant(Identifier("c"), Ind)

    val positiveCases = Seq(
      (Seq(Sequent(Set(q), Set(p, r))), LeftNot(Sequent(Set(q, neg(p)), Set(r)), 0, p)),
      (Seq(Sequent(Set(q), Set(neg(neg(p)), r))), LeftNot(Sequent(Set(q, neg(p)), Set(r)), 0, p))
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(q), Set(p, r))), LeftNot(Sequent(Set(neg(p)), Set(r)), 0, p)),
      (Seq(Sequent(Set(q), Set(p, r))), LeftNot(Sequent(Set(q, neg(p)), Set.empty), 0, p)),
      (Seq(Sequent(Set(q), Set(p, r))), LeftNot(Sequent(Set(q, neg(q)), Set(r)), 0, p)),
      (Seq(Sequent(Set(q), Set(p, r))), LeftNot(Sequent(Set(q, neg(p)), Set(r)), 0, c))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"LeftNot: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"LeftNot: negative case #${i + 1}", premises, step)
  }

  // ## case LeftForall(b, t1, phi, x, t) =>

  val leftForallTests = {
    val (p, q) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop)
    )
    val (x, y) = (
      Variable(Identifier("x"), Ind),
      Variable(Identifier("y"), Ind)
    )
    val P = Constant(Identifier("P"), Ind -> Prop)
    val c = Constant(Identifier("c"), Ind)
    val C = Constant(Identifier("C"), Prop)
    val phi = P(x)

    val positiveCases = Seq(
      (Seq(Sequent(Set(P(c), q), Set(p))), LeftForall(Sequent(Set(forall(Lambda(x, phi)), q), Set(p)), 0, phi, x, c)),
      (Seq(Sequent(Set(P(c), q), Set(p))), LeftForall(Sequent(Set(forall(Lambda(y, P(y))), q), Set(p)), 0, phi, x, c))
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(P(c), q), Set(p))), LeftForall(Sequent(Set(forall(Lambda(x, phi))), Set(p)), 0, phi, x, c)),
      (Seq(Sequent(Set(P(c), q), Set(p))), LeftForall(Sequent(Set(forall(Lambda(x, phi)), q), Set.empty), 0, phi, x, c)),
      (Seq(Sequent(Set(P(c), q), Set(p))), LeftForall(Sequent(Set(exists(Lambda(x, phi)), q), Set(p)), 0, phi, x, c)),
      (Seq(Sequent(Set(P(c), q), Set(p))), LeftForall(Sequent(Set(forall(Lambda(x, phi)), q), Set(p)), 0, c, x, c)),
      (Seq(Sequent(Set(P(c), q), Set(p))), LeftForall(Sequent(Set(forall(Lambda(x, phi)), q), Set(p)), 0, phi, x, C))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"LeftForall: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"LeftForall: negative case #${i + 1}", premises, step)
  }

  // ## case LeftExists(b, t1, phi, x) =>

  val leftExistsTests = {
    val p = Constant(Identifier("p"), Prop)
    val (x, y) = (
      Variable(Identifier("x"), Ind),
      Variable(Identifier("y"), Ind)
    )
    val P = Constant(Identifier("P"), Ind -> Prop)
    val c = Constant(Identifier("c"), Ind)
    val phi = P(x)

    val positiveCases = Seq(
      (Seq(Sequent(Set(P(x)), Set(p))), LeftExists(Sequent(Set(exists(Lambda(x, phi))), Set(p)), 0, phi, x)),
      (Seq(Sequent(Set(P(x)), Set(p))), LeftExists(Sequent(Set(exists(Lambda(y, P(y)))), Set(p)), 0, phi, x))
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(P(x)), Set(p))), LeftExists(Sequent(Set(exists(Lambda(x, phi)), P(x)), Set(p)), 0, phi, x)),
      (Seq(Sequent(Set(P(x)), Set(p))), LeftExists(Sequent(Set(forall(Lambda(x, phi))), Set(p)), 0, phi, x)),
      (Seq(Sequent(Set(P(x)), Set(p))), LeftExists(Sequent(Set(exists(Lambda(x, phi))), Set.empty), 0, phi, x)),
      (Seq(Sequent(Set(P(x)), Set(p))), LeftExists(Sequent(Set(exists(Lambda(x, phi))), Set(p)), 0, c, x))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"LeftExists: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"LeftExists: negative case #${i + 1}", premises, step)
  }

  // ## case RightAnd(b, t, cunjuncts) =>

  val rightAndTests = {
    val (p, q, r, s) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop),
      Constant(Identifier("r"), Prop),
      Constant(Identifier("s"), Prop)
    )
    val c = Constant(Identifier("c"), Ind)

    val positiveCases = Seq(
      (
        Seq(Sequent(Set(r), Set(p)), Sequent(Set(s), Set(q))),
        RightAnd(Sequent(Set(r, s), Set(and(p)(q))), Seq(0, 1), Seq(p, q))
      ),
      (
        Seq(Sequent(Set(r), Set(and(q)(p))), Sequent(Set(r), Set(s))),
        RightAnd(Sequent(Set(r), Set(and(and(p)(q))(s))), Seq(0, 1), Seq(and(p)(q), s))
      )
    )
    val negativeCases = Seq(
      (Seq.empty, RightAnd(Sequent(Set.empty, Set(and(p)(q))), Seq.empty, Seq.empty)),
      (Seq(Sequent(Set(r), Set(p))), RightAnd(Sequent(Set(r), Set(and(p)(q))), Seq(0), Seq(p, q))),
      (Seq(Sequent(Set(r), Set(p))), RightAnd(Sequent(Set(r), Set(and(p)(q))), Seq(0), Seq(c))),
      (Seq(Sequent(Set(r), Set(p)), Sequent(Set(s), Set(q))), RightAnd(Sequent(Set(r), Set(and(p)(q))), Seq(0, 1), Seq(p, q))),
      (Seq(Sequent(Set(r), Set(p)), Sequent(Set(s), Set(q))), RightAnd(Sequent(Set(r, s), Set(or(p)(q))), Seq(0, 1), Seq(p, q)))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"RightAnd: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"RightAnd: negative case #${i + 1}", premises, step)
  }

  // ## case RightOr(b, t1, phi, psi) =>

  val rightOrTests = {
    val (p, q, r, s) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop),
      Constant(Identifier("r"), Prop),
      Constant(Identifier("s"), Prop)
    )
    val c = Constant(Identifier("c"), Ind)

    val positiveCases = Seq(
      (Seq(Sequent(Set(r), Set(p, s))), RightOr(Sequent(Set(r), Set(or(p)(q), s)), 0, p, q)),
      (Seq(Sequent(Set(r), Set(and(q)(p), s))), RightOr(Sequent(Set(r), Set(or(and(p)(q))(q), s)), 0, and(p)(q), q))
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(r), Set(p, s))), RightOr(Sequent(Set(or(p)(q)), Set(or(p)(q), s)), 0, p, q)),
      (Seq(Sequent(Set(r), Set(p, s))), RightOr(Sequent(Set(r), Set(or(p)(q))), 0, p, q)),
      (Seq(Sequent(Set(r), Set(p, s))), RightOr(Sequent(Set(r), Set(and(p)(q), s)), 0, p, q)),
      (Seq(Sequent(Set(r), Set(p, s))), RightOr(Sequent(Set(r), Set(or(p)(q), s)), 0, c, q)),
      (Seq(Sequent(Set(and(q)(r)), Set(p))), RightOr(Sequent(Set(and(r)(q)), Set(or(p)(q))), 0, p, q))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"RightOr: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"RightOr: negative case #${i + 1}", premises, step)
  }

  // ## case RightImplies(b, t1, phi, psi) =>

  val rightImpliesTests = {
    val (p, q, r, s) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop),
      Constant(Identifier("r"), Prop),
      Constant(Identifier("s"), Prop)
    )
    val c = Constant(Identifier("c"), Ind)

    val positiveCases = Seq(
      (Seq(Sequent(Set(p, r), Set(q, s))), RightImplies(Sequent(Set(r), Set(implies(p)(q), s)), 0, p, q)),
      (Seq(Sequent(Set(neg(neg(p)), r), Set(and(q)(s)))), RightImplies(Sequent(Set(r), Set(implies(p)(and(s)(q)))), 0, p, and(q)(s)))
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(p, r), Set(q, s))), RightImplies(Sequent(Set.empty, Set(implies(p)(q), s)), 0, p, q)),
      (Seq(Sequent(Set(p, r), Set(q, s))), RightImplies(Sequent(Set(r), Set(implies(p)(q))), 0, p, q)),
      (Seq(Sequent(Set(p, r), Set(q, s))), RightImplies(Sequent(Set(r), Set(implies(q)(p), s)), 0, p, q)),
      (Seq(Sequent(Set(p, r), Set(q, s))), RightImplies(Sequent(Set(r), Set(implies(p)(q), s)), 0, c, q))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"RightImplies: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"RightImplies: negative case #${i + 1}", premises, step)
  }

  // ## case RightIff(b, t1, t2, phi, psi) =>

  val rightIffTests = {
    val (p, q, r, s) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop),
      Constant(Identifier("r"), Prop),
      Constant(Identifier("s"), Prop)
    )
    val c = Constant(Identifier("c"), Ind)

    val positiveCases = Seq(
      (
        Seq(Sequent(Set(r), Set(implies(p)(q), s)), Sequent(Set(r), Set(implies(q)(p), s))),
        RightIff(Sequent(Set(r), Set(iff(p)(q), s)), 0, 1, p, q)
      ),
      (
        Seq(Sequent(Set(r), Set(or(neg(p))(q))), Sequent(Set(s), Set(or(neg(q))(p)))),
        RightIff(Sequent(Set(r, s), Set(iff(p)(q))), 0, 1, p, q)
      )
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(r), Set(implies(p)(q))), Sequent(Set(s), Set(implies(q)(p)))), RightIff(Sequent(Set(r), Set(iff(p)(q))), 0, 1, p, q)),
      (Seq(Sequent(Set(r), Set(implies(p)(q))), Sequent(Set(s), Set(implies(q)(p)))), RightIff(Sequent(Set(r, s), Set.empty), 0, 1, p, q)),
      (Seq(Sequent(Set(r), Set(implies(p)(q))), Sequent(Set(s), Set(implies(q)(p)))), RightIff(Sequent(Set(r, s), Set(iff(p)(r))), 0, 1, p, q)),
      (Seq(Sequent(Set(r), Set(implies(p)(q))), Sequent(Set(s), Set(implies(q)(p)))), RightIff(Sequent(Set(r, s), Set(iff(p)(q))), 0, 1, c, q))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"RightIff: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"RightIff: negative case #${i + 1}", premises, step)
  }

  // ## case RightNot(b, t1, phi) =>

  val rightNotTests = {
    val (p, q, r) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop),
      Constant(Identifier("r"), Prop)
    )
    val c = Constant(Identifier("c"), Ind)

    val positiveCases = Seq(
      (Seq(Sequent(Set(p, q), Set(r))), RightNot(Sequent(Set(q), Set(neg(p), r)), 0, p)),
      (Seq(Sequent(Set(neg(neg(p)), q), Set(r))), RightNot(Sequent(Set(q), Set(neg(p), r)), 0, p))
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(p, q), Set(r))), RightNot(Sequent(Set(q), Set(neg(p))), 0, p)),
      (Seq(Sequent(Set(p, q), Set(r))), RightNot(Sequent(Set(q), Set(neg(q), r)), 0, p)),
      (Seq(Sequent(Set(p, q), Set(r))), RightNot(Sequent(Set(q), Set(neg(p), r)), 0, c)),
      (Seq(Sequent(Set(p), Set(and(q)(r)))), RightNot(Sequent(Set.empty, Set(neg(p), and(r)(q))), 0, p))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"RightNot: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"RightNot: negative case #${i + 1}", premises, step)
  }

  // ## case RightForall(b, t1, phi, x) =>

  val rightForallTests = {
    val p = Constant(Identifier("p"), Prop)
    val (x, y) = (
      Variable(Identifier("x"), Ind),
      Variable(Identifier("y"), Ind)
    )
    val P = Constant(Identifier("P"), Ind -> Prop)
    val c = Constant(Identifier("c"), Ind)
    val phi = P(x)

    val positiveCases = Seq(
      (Seq(Sequent(Set(p), Set(P(x)))), RightForall(Sequent(Set(p), Set(forall(Lambda(x, phi)))), 0, phi, x)),
      (Seq(Sequent(Set(p), Set(P(x)))), RightForall(Sequent(Set(p), Set(forall(Lambda(y, P(y))))), 0, phi, x))
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(p), Set(P(x)))), RightForall(Sequent(Set(p, P(x)), Set(forall(Lambda(x, phi)))), 0, phi, x)),
      (Seq(Sequent(Set(p), Set(P(x)))), RightForall(Sequent(Set(p), Set(exists(Lambda(x, phi)))), 0, phi, x)),
      (Seq(Sequent(Set(p), Set(P(x)))), RightForall(Sequent(Set(p), Set(forall(Lambda(x, phi)), P(x))), 0, phi, x)),
      (Seq(Sequent(Set(p), Set(P(x)))), RightForall(Sequent(Set(p), Set(forall(Lambda(x, phi)))), 0, c, x))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"RightForall: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"RightForall: negative case #${i + 1}", premises, step)
  }

  // ## case RightExists(b, t1, phi, x, t) =>

  val rightExistsTests = {
    val p = Constant(Identifier("p"), Prop)
    val (x, y) = (
      Variable(Identifier("x"), Ind),
      Variable(Identifier("y"), Ind)
    )
    val P = Constant(Identifier("P"), Ind -> Prop)
    val c = Constant(Identifier("c"), Ind)
    val C = Constant(Identifier("C"), Prop)
    val phi = P(x)

    val positiveCases = Seq(
      (Seq(Sequent(Set(p), Set(P(c)))), RightExists(Sequent(Set(p), Set(exists(Lambda(x, phi)))), 0, phi, x, c)),
      (Seq(Sequent(Set(p), Set(P(c)))), RightExists(Sequent(Set(p), Set(exists(Lambda(y, P(y))))), 0, phi, x, c))
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(p), Set(P(c)))), RightExists(Sequent(Set.empty, Set(exists(Lambda(x, phi)))), 0, phi, x, c)),
      (Seq(Sequent(Set(p), Set(P(c)))), RightExists(Sequent(Set(p), Set(forall(Lambda(x, phi)))), 0, phi, x, c)),
      (Seq(Sequent(Set(p), Set(P(c)))), RightExists(Sequent(Set(p), Set(exists(Lambda(x, phi)))), 0, phi, x, C)),
      (Seq(Sequent(Set(p), Set(P(c)))), RightExists(Sequent(Set(p), Set(exists(Lambda(x, phi)))), 0, c, x, c))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"RightExists: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"RightExists: negative case #${i + 1}", premises, step)
  }

  // ## case RightEpsilon(b, t1, phi, x, t) =>

  val rightEpsilonTests = {
    val p = Constant(Identifier("p"), Prop)
    val x = Variable(Identifier("x"), Ind)
    val P = Constant(Identifier("P"), Ind -> Prop)
    val c = Constant(Identifier("c"), Ind)
    val C = Constant(Identifier("C"), Prop)
    val phi = P(x)
    val epsPhi = epsilon(Lambda(x, phi))

    val positiveCases = Seq(
      (Seq(Sequent(Set(p), Set(P(c)))), RightEpsilon(Sequent(Set(p), Set(P(epsPhi))), 0, phi, x, c))
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(p), Set(P(c)))), RightEpsilon(Sequent(Set.empty, Set(P(epsPhi))), 0, phi, x, c)),
      (Seq(Sequent(Set(p), Set(P(c)))), RightEpsilon(Sequent(Set(p), Set(P(c))), 0, phi, x, c)),
      (Seq(Sequent(Set(p), Set(P(c)))), RightEpsilon(Sequent(Set(p), Set(P(epsPhi))), 0, phi, x, C)),
      (Seq(Sequent(Set(p), Set(P(c)))), RightEpsilon(Sequent(Set(p), Set(P(epsPhi))), 0, c, x, c))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"RightEpsilon: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"RightEpsilon: negative case #${i + 1}", premises, step)
  }

  // ## case Weakening(b, t1) =>

  val weakeningTests = {
    val (p, q, r, s) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop),
      Constant(Identifier("r"), Prop),
      Constant(Identifier("s"), Prop)
    )

    val positiveCases = Seq(
      (Seq(Sequent(Set(p), Set(q))), Weakening(Sequent(Set(p, r), Set(q, s)), 0)),
      (Seq(Sequent(Set(and(p)(q)), Set(r))), Weakening(Sequent(Set(and(q)(p)), Set(r)), 0))
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(p), Set(q))), Weakening(Sequent(Set.empty, Set(q)), 0)),
      (Seq(Sequent(Set(p), Set(q))), Weakening(Sequent(Set(p), Set.empty), 0))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"Weakening: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"Weakening: negative case #${i + 1}", premises, step)
  }

  // ## case LeftRefl(b, t1, phi) =>

  val leftReflTests = {
    val p = Constant(Identifier("p"), Prop)
    val (x, y) = (
      Variable(Identifier("x"), Ind),
      Variable(Identifier("y"), Ind)
    )
    val P = Constant(Identifier("P"), Ind -> Prop)
    val epsX = epsilon(Lambda(x, P(x)))
    val epsY = epsilon(Lambda(y, P(y)))

    val positiveCases = Seq(
      (Seq(Sequent(Set(equality(x)(x), p), Set(p))), LeftRefl(Sequent(Set(p), Set(p)), 0, equality(x)(x))),
      (Seq(Sequent(Set(equality(epsX)(epsY)), Set(p))), LeftRefl(Sequent(Set.empty, Set(p)), 0, equality(epsX)(epsY)))
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(equality(x)(y), p), Set(p))), LeftRefl(Sequent(Set(p), Set(p)), 0, equality(x)(y))),
      (Seq(Sequent(Set(equality(x)(x), p), Set(p))), LeftRefl(Sequent(Set(p), Set.empty), 0, equality(x)(x))),
      (Seq(Sequent(Set(p), Set(p))), LeftRefl(Sequent(Set.empty, Set(p)), 0, p))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"LeftRefl: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"LeftRefl: negative case #${i + 1}", premises, step)
  }

  // ## case RightRefl(b, phi) =>

  val rightReflTests = {
    val (x, y) = (
      Variable(Identifier("x"), Ind),
      Variable(Identifier("y"), Ind)
    )
    val p = Constant(Identifier("p"), Prop)
    val P = Constant(Identifier("P"), Ind -> Prop)
    val epsX = epsilon(Lambda(x, P(x)))
    val epsY = epsilon(Lambda(y, P(y)))

    val positiveCases = Seq(
      RightRefl(Sequent(Set.empty, Set(equality(x)(x))), equality(x)(x)),
      RightRefl(Sequent(Set.empty, Set(equality(epsX)(epsY))), equality(epsX)(epsY))
    )
    val negativeCases = Seq(
      RightRefl(Sequent(Set.empty, Set(equality(x)(y))), equality(x)(y)),
      RightRefl(Sequent(Set.empty, Set.empty), equality(x)(x)),
      RightRefl(Sequent(Set.empty, Set(p)), p)
    )

    for ((step, i) <- positiveCases.zipWithIndex) posTest(s"RightRefl: positive case #${i + 1}", Seq.empty, step)
    for ((step, i) <- negativeCases.zipWithIndex) negTest(s"RightRefl: negative case #${i + 1}", Seq.empty, step)
  }

  // ## case LeftSubstEq(b, t1, equals, lambdaPhi) =>

  val leftSubstEqTests = {
    val p = Constant(Identifier("p"), Prop)
    val q = Constant(Identifier("q"), Prop)
    val (x, y, z) = (
      Variable(Identifier("x"), Ind),
      Variable(Identifier("y"), Ind),
      Variable(Identifier("z"), Ind)
    )
    val P = Constant(Identifier("P"), Ind -> Prop)
    val T = Variable(Identifier("T"), Ind)
    val X = Variable(Identifier("X"), Prop)
    val F = Variable(Identifier("F"), Ind -> Ind)
    val (f, g) = (
      Constant(Identifier("f"), Ind -> Ind),
      Constant(Identifier("g"), Ind -> Ind)
    )

    val positiveCases = Seq(
      (Seq(Sequent(Set(P(x)), Set(p))), LeftSubstEq(Sequent(Set(P(y), equality(x)(y)), Set(p)), 0, Seq((x, y)), (Seq(T), P(T)))),
      (Seq(Sequent(Set(P(x), p), Set(p))), LeftSubstEq(Sequent(Set(P(y), p, equality(x)(y)), Set(p)), 0, Seq((x, y)), (Seq(T), P(T)))),
      (Seq(Sequent(Set(or(p)(equality(z)(z))), Set(p))), LeftSubstEq(Sequent(Set(or(q)(equality(z)(z)), iff(p)(q)), Set(p)), 0, Seq((p, q)), (Seq(X), or(X)(equality(z)(z))))),
      (Seq(Sequent(Set(P(f(x))), Set(p))), LeftSubstEq(Sequent(Set(P(g(x)), forall(Lambda(z, equality(f(z))(g(z))))), Set(p)), 0, Seq((f, g)), (Seq(F), P(F(x)))))
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(P(x)), Set(p))), LeftSubstEq(Sequent(Set(P(y)), Set(p)), 0, Seq((x, y)), (Seq(T), P(T)))),
      (Seq(Sequent(Set(P(x)), Set(p))), LeftSubstEq(Sequent(Set(P(z), equality(x)(y)), Set(p)), 0, Seq((x, y)), (Seq(T), P(T)))),
      (Seq(Sequent(Set(P(x)), Set(p))), LeftSubstEq(Sequent(Set(P(y), equality(x)(y)), Set.empty), 0, Seq((x, y)), (Seq(T), P(T)))),
      (Seq(Sequent(Set(P(x)), Set(p))), LeftSubstEq(Sequent(Set(P(y), equality(x)(y)), Set(p)), 0, Seq((x, y)), (Seq(T, z), P(T)))),
      (Seq(Sequent(Set(or(p)(equality(z)(z))), Set(p))), LeftSubstEq(Sequent(Set(or(q)(equality(z)(z))), Set(p)), 0, Seq((p, q)), (Seq(X), or(X)(equality(z)(z))))),
      (Seq(Sequent(Set(P(f(x))), Set(p))), LeftSubstEq(Sequent(Set(P(g(x)), equality(f(x))(g(x))), Set(p)), 0, Seq((f, g)), (Seq(F), P(F(x)))))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"LeftSubstEq: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"LeftSubstEq: negative case #${i + 1}", premises, step)
  }

  // ## case RightSubstEq(b, t1, equals, lambdaPhi) =>

  val rightSubstEqTests = {
    val p = Constant(Identifier("p"), Prop)
    val q = Constant(Identifier("q"), Prop)
    val (x, y, z) = (
      Variable(Identifier("x"), Ind),
      Variable(Identifier("y"), Ind),
      Variable(Identifier("z"), Ind)
    )
    val P = Constant(Identifier("P"), Ind -> Prop)
    val T = Variable(Identifier("T"), Ind)
    val X = Variable(Identifier("X"), Prop)
    val F = Variable(Identifier("F"), Ind -> Ind)
    val (f, g) = (
      Constant(Identifier("f"), Ind -> Ind),
      Constant(Identifier("g"), Ind -> Ind)
    )

    val positiveCases = Seq(
      (Seq(Sequent(Set(p), Set(P(x)))), RightSubstEq(Sequent(Set(p, equality(x)(y)), Set(P(y))), 0, Seq((x, y)), (Seq(T), P(T)))),
      (Seq(Sequent(Set(p), Set(P(x), p))), RightSubstEq(Sequent(Set(p, equality(x)(y)), Set(P(y), p)), 0, Seq((x, y)), (Seq(T), P(T)))),
      (Seq(Sequent(Set(p), Set(or(p)(equality(z)(z))))), RightSubstEq(Sequent(Set(p, iff(p)(q)), Set(or(q)(equality(z)(z)))), 0, Seq((p, q)), (Seq(X), or(X)(equality(z)(z))))),
      (Seq(Sequent(Set(p), Set(P(f(x))))), RightSubstEq(Sequent(Set(p, forall(Lambda(z, equality(f(z))(g(z))))), Set(P(g(x)))), 0, Seq((f, g)), (Seq(F), P(F(x)))))
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(p), Set(P(x)))), RightSubstEq(Sequent(Set(p), Set(P(y))), 0, Seq((x, y)), (Seq(T), P(T)))),
      (Seq(Sequent(Set(p), Set(P(x)))), RightSubstEq(Sequent(Set(p, equality(x)(y)), Set(P(z))), 0, Seq((x, y)), (Seq(T), P(T)))),
      (Seq(Sequent(Set(p), Set(P(x)))), RightSubstEq(Sequent(Set(equality(x)(y)), Set(P(y))), 0, Seq((x, y)), (Seq(T), P(T)))),
      (Seq(Sequent(Set(p), Set(P(x)))), RightSubstEq(Sequent(Set(p, equality(x)(y)), Set(P(y))), 0, Seq((x, y)), (Seq(T, z), P(T)))),
      (Seq(Sequent(Set(p), Set(or(p)(equality(z)(z))))), RightSubstEq(Sequent(Set(p), Set(or(q)(equality(z)(z)))), 0, Seq((p, q)), (Seq(X), or(X)(equality(z)(z))))),
      (Seq(Sequent(Set(p), Set(P(f(x))))), RightSubstEq(Sequent(Set(p, equality(f(x))(g(x))), Set(P(g(x)))), 0, Seq((f, g)), (Seq(F), P(F(x)))))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"RightSubstEq: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"RightSubstEq: negative case #${i + 1}", premises, step)
  }

  // ## case InstSchema(bot, t1, subst) =>

  val instSchemaTests = {
    val (p, q, r) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop),
      Constant(Identifier("r"), Prop)
    )
    val X = Variable(Identifier("X"), Prop)
    val x = Variable(Identifier("x"), Ind)

    val positiveCases = Seq(
      (Seq(Sequent(Set(X), Set(X))), InstSchema(Sequent(Set(and(p)(q)), Set(and(q)(p))), 0, Map(X -> and(p)(q)))),
      (Seq(Sequent(Set(X), Set(r))), InstSchema(Sequent(Set(and(p)(q)), Set(r)), 0, Map(X -> and(q)(p))))
    )
    val negativeCases = Seq(
      (Seq(Sequent(Set(X), Set(X))), InstSchema(Sequent(Set(and(p)(q)), Set(r)), 0, Map(X -> and(p)(q)))),
      (Seq(Sequent(Set(X), Set(X))), InstSchema(Sequent(Set(X), Set(X)), 0, Map(X -> x)))
    )

    for (((premises, step), i) <- positiveCases.zipWithIndex) posTest(s"InstSchema: positive case #${i + 1}", premises, step)
    for (((premises, step), i) <- negativeCases.zipWithIndex) negTest(s"InstSchema: negative case #${i + 1}", premises, step)
  }

  val subproofTests = {
    val (p, q) = (
      Constant(Identifier("p"), Prop),
      Constant(Identifier("q"), Prop)
    )
    val sp = SCProof(IndexedSeq(Restate(Sequent(Set(p), Set(q)), -1)), IndexedSeq(Sequent(Set(p), Set(q))))

    posTest("SCSubproof: positive case #1", Seq(Sequent(Set(p), Set(q))), SCSubproof(sp, Seq(0)))
    posTest("SCSubproof: positive case #2", Seq(Sequent(Set(and(p)(q)), Set(p))), SCSubproof(SCProof(IndexedSeq(Restate(Sequent(Set(and(q)(p)), Set(p)), -1)), IndexedSeq(Sequent(Set(and(q)(p)), Set(p)))), Seq(0)))
    negTest("SCSubproof: negative case #1", Seq(Sequent(Set(q), Set(p))), SCSubproof(sp, Seq(0)))
    negTest("SCSubproof: negative case #2", Seq(Sequent(Set(p), Set(q))), SCSubproof(sp, Seq.empty))
  }

  // ## case Sorry(b) =>

  val sorryTests = {
    val p = Constant(Identifier("p"), Prop)
    posTest("Sorry: positive case #1", Seq.empty, Sorry(Sequent(Set.empty, Set(p))))
  }

}
