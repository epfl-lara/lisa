package lisa.kernel

import lisa.kernel.fol.FOL._
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
          Sequent(Set(r), Set(s))
        ),
        Cut(Sequent(Set(p, r), Set(s)), 0, 1, q)
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

  // ## case LeftOr(b, t, disjuncts) =>

  // ## case LeftImplies(b, t1, t2, phi, psi) =>

  // ## case LeftIff(b, t1, phi, psi) =>

  // ## case LeftNot(b, t1, phi) =>

  // ## case LeftForall(b, t1, phi, x, t) =>

  // ## case LeftExists(b, t1, phi, x) =>

  // ## case RightAnd(b, t, cunjuncts) =>

  // ## case RightOr(b, t1, phi, psi) =>

  // ## case RightImplies(b, t1, phi, psi) =>

  // ## case RightIff(b, t1, t2, phi, psi) =>

  // ## case RightNot(b, t1, phi) =>

  // ## case RightForall(b, t1, phi, x) =>

  // ## case RightExists(b, t1, phi, x, t) =>

  // ## case RightEpsilon(b, t1, phi, x, t) =>

  // ## case Weakening(b, t1) =>

  // ## case LeftRefl(b, t1, phi) =>

  // ## case RightRefl(b, phi) =>

  // ## case LeftSubstEq(b, t1, equals, lambdaPhi) =>

  // ## case RightSubstEq(b, t1, equals, lambdaPhi) =>

  // ## case InstSchema(bot, t1, subst) =>

  // ## case Sorry(b) =>

}
