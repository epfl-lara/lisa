package lisa.automation.clausification

import lisa.automation.ProofSyntax.{_, given}

import scala.collection.mutable

/**
 * Derive ⊢ NNF(f) from the single import ⊢ f using the sequent rules for f's connectives.
 */
private[clausification] object NnfProof:
  def apply(f: Expression): ProofCertificate = new Builder().prove(f)

  // Positive induction proves f ⊢ NNF(f). Negative induction proves ⊢ f, NNF(¬f).
  private case class Result(normal: Expression, ref: Int)

  private final class Builder:
    private val steps = mutable.ArrayBuffer.empty[ProofStep]
    private val memo = mutable.Map.empty[(Expression, Boolean), Result]

    // These are the two nullary logical rules in Lisa's certificate vocabulary.
    private lazy val trueRight = emit(RestateTrue(() |- top))
    private lazy val falseLeft = emit(RestateTrue(bot |- ()))

    private def emit(step: ProofStep): Int =
      steps += step
      steps.size - 1

    def prove(f: Expression): ProofCertificate =
      val result = derive(f, negative = false)
      emit(Cut(() |- result.normal, -1, result.ref, f))
      ProofCertificate(steps.toVector, Vector(() |- f))

    private def weaken(ref: Int, goal: Sequent): Int =
      if steps(ref).statement == goal then ref else emit(Weakening(goal, ref))

    /**
     * After a right introduction, account for the NNF simplifications involving ⊤ or ⊥.
     */
    private def join(context: Sequent, a: Expression, b: Expression, conjunction: Boolean)(intro: Sequent => Int): Result =
      val raw = if conjunction then and(a)(b) else or(a)(b)
      val normal = if conjunction then NnfPhase.mkAnd(a, b) else NnfPhase.mkOr(a, b)
      val rawRef = intro(context +>> raw)
      if normal == raw then Result(raw, rawRef)
      else
        val goal = raw |- normal
        val reduction =
          if conjunction then
            val both = emit(Hypothesis((a, b) |- normal, normal))
            emit(LeftAnd(goal, both, a, b))
          else
            def branch(f: Expression): Int =
              if f == normal then emit(Hypothesis(f |- normal, f))
              else if f == bot then weaken(falseLeft, f |- normal)
              else weaken(trueRight, f |- normal)
            emit(LeftOr(goal, Seq(branch(a), branch(b)), Seq(a, b)))
        Result(normal, emit(Cut(context +>> normal, rawRef, reduction, raw)))

    private def derive(f: Expression, negative: Boolean): Result = memo.getOrElseUpdate(
      (f, negative), {
        Clausification.checkInterrupted()
        f match
          case Neg(a) =>
            val child = derive(a, !negative)
            val ref =
              if negative then emit(RightNot(() |- (f, child.normal), child.ref, a))
              else emit(LeftNot(f |- child.normal, child.ref, a))
            Result(child.normal, ref)
          case And(a, b) => connective(f, a, b, sourceAnd = true, negative)
          case Or(a, b) => connective(f, a, b, sourceAnd = false, negative)
          case Implies(a, b) => implication(a, b, negative, swap = false)
          case Iff(a, b) => biconditional(f, a, b, negative)
          case Forall(x, body) => quantifier(f, x, body, universal = true, negative)
          case Exists(x, body) => quantifier(f, x, body, universal = false, negative)
          case atom if !negative => Result(atom, emit(Hypothesis(atom |- atom, atom)))
          case atom if atom == top || atom == bot =>
            val normal = if atom == top then bot else top
            Result(normal, weaken(trueRight, () |- (atom, normal)))
          case atom =>
            val id = emit(Hypothesis(atom |- atom, atom))
            Result(neg(atom), emit(RightNot(() |- (atom, neg(atom)), id, atom)))
      }
    )

    private def connective(f: Expression, a: Expression, b: Expression, sourceAnd: Boolean, negative: Boolean): Result =
      val l = derive(a, negative)
      val r = derive(b, negative)
      val context = if negative then () |- f else f |- ()
      join(context, l.normal, r.normal, conjunction = sourceAnd != negative): goal =>
        if !negative && sourceAnd then
          val pair = emit(RightAnd(Sequent(Set(a, b), goal.right), Seq(l.ref, r.ref), Seq(l.normal, r.normal)))
          emit(LeftAnd(goal, pair, a, b))
        else if !negative then
          val cases = emit(LeftOr(f |- (l.normal, r.normal), Seq(l.ref, r.ref), Seq(a, b)))
          emit(RightOr(goal, cases, l.normal, r.normal))
        else if sourceAnd then
          val pair = emit(RightAnd(() |- (f, l.normal, r.normal), Seq(l.ref, r.ref), Seq(a, b)))
          emit(RightOr(goal, pair, l.normal, r.normal))
        else
          val pair = emit(RightAnd(() |- (a, b, and(l.normal)(r.normal)), Seq(l.ref, r.ref), Seq(l.normal, r.normal)))
          emit(RightOr(goal, pair, a, b))

    /**
     * The second implication in an iff uses the opposite operand order in the clausifier's NNF.
     */
    private def implication(a: Expression, b: Expression, negative: Boolean, swap: Boolean): Result =
      val l = derive(a, !negative)
      val r = derive(b, negative)
      val (first, second) = if swap then (r, l) else (l, r)
      val imp = implies(a)(b)
      val context = if negative then () |- imp else imp |- ()
      join(context, first.normal, second.normal, conjunction = negative): goal =>
        if negative then
          val pair = emit(RightAnd(a |- (b, and(first.normal)(second.normal)), Seq(first.ref, second.ref), Seq(first.normal, second.normal)))
          emit(RightImplies(goal, pair, a, b))
        else
          val cases = emit(LeftImplies(imp |- (l.normal, r.normal), l.ref, r.ref, a, b))
          emit(RightOr(goal, cases, first.normal, second.normal))

    private def biconditional(f: Expression, a: Expression, b: Expression, negative: Boolean): Result =
      val forward = implication(a, b, negative, swap = false)
      val backward = implication(b, a, negative, swap = true)
      val context = if negative then () |- f else f |- ()
      join(context, forward.normal, backward.normal, conjunction = !negative): goal =>
        if negative then
          val eq = emit(RightIff(() |- (f, forward.normal, backward.normal), forward.ref, backward.ref, a, b))
          emit(RightOr(goal, eq, forward.normal, backward.normal))
        else
          val pair = emit(RightAnd(Sequent(Set(implies(a)(b), implies(b)(a)), goal.right), Seq(forward.ref, backward.ref), Seq(forward.normal, backward.normal)))
          emit(LeftIff(goal, pair, a, b))

    private def quantifier(f: Expression, x: Variable, body: Expression, universal: Boolean, negative: Boolean): Result =
      val child = derive(body, negative)
      val n = child.normal
      val normal = if universal != negative then forall(x, n) else exists(x, n)
      val ref =
        if !negative && universal then
          val opened = emit(LeftForall(f |- n, child.ref, body, x, x))
          emit(RightForall(f |- normal, opened, n, x))
        else if !negative then
          val closed = emit(RightExists(body |- normal, child.ref, n, x, x))
          emit(LeftExists(f |- normal, closed, body, x))
        else if universal then
          val closed = emit(RightExists(() |- (body, normal), child.ref, n, x, x))
          emit(RightForall(() |- (f, normal), closed, body, x))
        else
          val closed = emit(RightExists(() |- (f, n), child.ref, body, x, x))
          emit(RightForall(() |- (f, normal), closed, n, x))
      Result(normal, ref)
