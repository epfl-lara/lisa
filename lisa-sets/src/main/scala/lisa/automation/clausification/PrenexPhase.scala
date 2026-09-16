package lisa.automation.clausification

import lisa.automation.Problem
import lisa.utils.K.{_, given}

import Clausification._

/**
 * Universal-quantifier stripping: replace each `∀x. …` by its body with `x` at a fresh clause variable `w`,
 * leaving [[DistributePhase]] a quantifier-free matrix. Quantifiers are not necessarily at the root
 * [[provePrenex]] applies `LeftForall` at each `∀` in place, walking the formula's
 * tree and mirroring its connectives, which costs a proof linear in `|φ|`.
 */
private[clausification] object PrenexPhase:

  /**
   * For each axiom containing a `∀` anywhere in its tree, strip all universals, instantiating each at a fresh
   * clause variable `w` (pre-order) via `LeftForall`. Certifies the derivation of the quantifier-free matrix
   * via [[provePrenex]].
   */
  def certifyPrenex(problem: Problem, prover: ClausificationProver, goal: Set[Int] = Set.empty)(using ClausifierOptions): ClausificationProof = {
    require(problem.conjecture.isEmpty, "certifyPrenex expects a conjecture-free problem (consumed by certifyNegated)")
    val counter = Counter()
    val hypotheses = problem.hypotheses.toIndexedSeq
    val n = hypotheses.size

    val steps = scala.collection.mutable.ArrayBuffer.empty[ClausificationProofStep]
    val matrices = scala.collection.mutable.ArrayBuffer.empty[Sequent]
    val matrixRefs = scala.collection.mutable.ArrayBuffer.empty[Int]
    for i <- 0 until n do
      checkInterrupted()
      val ax = hypotheses(i)
      val phi = singleRightFormula(ax, "axiom")
      if !hasForall(phi) then
        matrices += ax
        matrixRefs += -(i + 1)
      else
        // The step derives `() ⊢ matrix` from the axiom import, instantiating each stripped `∀` at a fresh
        // clause variable `w`; the matrix it arrives at is the axiom handed downstream.
        val (sub, matrixAx) = provePrenex(ax, -(i + 1), counter, n)
        steps += sub
        matrices += matrixAx
        matrixRefs += steps.size - 1

    val newProblem = Problem(matrices.toList, None, problem.frozen)
    require(matrices.size == problem.hypotheses.size, "prenex must map hypotheses one-to-one: the goal travels as a hypothesis index")
    val downstream = prover(newProblem, goal)
    require(sameImportList(downstream.imports, newProblem.imports ++ libImports), "Downstream imports must match transformed problem imports")
    steps += ClausificationSubproof(downstream, matrixRefs.toIndexedSeq ++ libRefs(n))
    ClausificationProof(steps.toIndexedSeq, hypotheses ++ libImports)
  }

  def hasForall(f: Expression): Boolean = f match
    case Forall(_, _) => true
    case And(g, h) => hasForall(g) || hasForall(h)
    case Or(g, h) => hasForall(g) || hasForall(h)
    case Neg(g) => hasForall(g)
    case _ => false

  /**
   * Build a kernel proof of `() ⊢ matrix` from the imported `() ⊢ phi`, where `matrix` is `phi` with every
   * `∀x._` stripped and `x` replaced by a fresh clause variable `w` drawn from `counter`, and return it with
   * that matrix. Walks `phi`'s tree, mirroring its connectives and using `LeftForall` at each universal to
   * instantiate it, then `Cut`s against `imported`.
   *
   * Proof size is linear in `|phi|`.
   */
  def provePrenex(imported: Sequent, premise: Int, counter: Counter, nonLibSize: Int)(using o: ClausifierOptions): (SCSubproof, Sequent) =
    o.prenex match
      case Prenex.Deconstruct => byDeconstruction(imported, premise, counter)
      case Prenex.Rewrite => byRewriting(imported, premise, counter, nonLibSize)

  private def byDeconstruction(imported: Sequent, premise: Int, counter: Counter): (SCSubproof, Sequent) = {
    val phi = singleRightFormula(imported, "imported (prenex source)")

    val steps = scala.collection.mutable.ArrayBuffer.empty[SCProofStep]
    def emit(s: SCProofStep): Int = { steps += s; steps.size - 1 }

    /**
     * `Hypothesis(e ⊢ e)`, the derivation of a subformula whose matrix is itself.
     */
    def hypothesis(e: Expression): Int = emit(Hypothesis(e |- e, e))

    // Builds steps with conclusion `orig ⊢ matrixOf(orig)` and returns the step index, or `None` when `orig`
    // holds no ∀ and so needs no derivation at all: its matrix is itself, and the parent emits the one
    // `Hypothesis` where it needs an index.
    def go(orig: Expression): Option[Int] = orig match
      case Forall(x, body) =>
        val v = Variable(Identifier(GeneratedNames.clauseVar, counter.next()), Ind)
        val bodySub = substituteVariablesOpti(body, Map(x -> v))
        val innerIdx = go(bodySub).getOrElse(hypothesis(bodySub))
        val innerM = steps(innerIdx).bot.right.head
        // LeftForall(b, t1, phi, x, t): from `Γ, body[x:=v] ⊢ Δ` derive `Γ, ∀x.body ⊢ Δ`.
        Some(emit(LeftForall(orig |- innerM, innerIdx, body, x, v)))

      case And(g, h) =>
        (go(g), go(h)) match
          case (None, None) => None
          case (og, oh) =>
            val gIdx = og.getOrElse(hypothesis(g))
            val hIdx = oh.getOrElse(hypothesis(h))
            val mg = steps(gIdx).bot.right.head
            val mh = steps(hIdx).bot.right.head
            val mAnd = and(mg)(mh)
            val gWithAnd = emit(LeftAnd(orig |- mg, gIdx, g, h))
            val hWithAnd = emit(LeftAnd(orig |- mh, hIdx, g, h))
            Some(emit(RightAnd(orig |- mAnd, Seq(gWithAnd, hWithAnd), Seq(mg, mh))))

      case Or(g, h) =>
        (go(g), go(h)) match
          case (None, None) => None
          case (og, oh) =>
            val gIdx = og.getOrElse(hypothesis(g))
            val hIdx = oh.getOrElse(hypothesis(h))
            val mg = steps(gIdx).bot.right.head
            val mh = steps(hIdx).bot.right.head
            val mOr = or(mg)(mh)
            // RightOr lifts each branch to the disjunctive matrix; LeftOr combines them.
            val gWithOr = emit(RightOr(g |- mOr, gIdx, mg, mh))
            val hWithOr = emit(RightOr(h |- mOr, hIdx, mg, mh))
            Some(emit(LeftOr(orig |- mOr, Seq(gWithOr, hWithOr), Seq(g, h))))

      case _ => None // NNF leaves: atoms and negated atoms, which hold no ∀

    val phiToMatrixIdx = go(phi).getOrElse(hypothesis(phi))
    val matrix = steps(phiToMatrixIdx).bot.right.head
    // Cut: from `() ⊢ phi` (import 0) and `phi ⊢ matrix` derive `() ⊢ matrix`.
    emit(Cut(() |- matrix, -1, phiToMatrixIdx, phi))

    (SCSubproof(SCProof(steps.toIndexedSeq, IndexedSeq(imported)), IndexedSeq(premise)), () |- matrix)
  }

  /**
   * One `∧` or `∨` on the path from the root to a `∀`, the side the `∀` is on, and the other operand.
   */
  private case class Layer(conj: Boolean, onLeft: Boolean, sibling: Expression)

  /**
   * Lift each `∀` to the root one connective at a time with the four prenex laws, then strip it there. Costs
   * quantifiers times depth rather than `|phi|`.
   */
  private def byRewriting(imported: Sequent, premise: Int, counter: Counter, nonLibSize: Int): (SCSubproof, Sequent) =
    val phi = singleRightFormula(imported, "imported (prenex source)")
    val steps = scala.collection.mutable.ArrayBuffer.empty[SCProofStep]
    def emit(s: SCProofStep): Int = { steps += s; steps.size - 1 }
    val holes = Counter()

    // The laws are inner imports `-2` to `-5`, in `libImports` order.
    def lawRef(l: Layer): Int = -(2 + (if l.conj then 0 else 2) + (if l.onLeft then 0 else 1))

    /**
     * The leftmost `∀` in pre-order, with the path of connective layers from the root down to it.
     */
    def locate(f: Expression): Option[(List[Layer], Variable, Expression)] = f match
      case Forall(x, body) => Some((Nil, x, body))
      case And(g, h) =>
        locate(g)
          .map((p, x, b) => (Layer(true, true, h) :: p, x, b))
          .orElse(locate(h).map((p, x, b) => (Layer(true, false, g) :: p, x, b)))
      case Or(g, h) =>
        locate(g)
          .map((p, x, b) => (Layer(false, true, h) :: p, x, b))
          .orElse(locate(h).map((p, x, b) => (Layer(false, false, g) :: p, x, b)))
      case _ => None

    /**
     * `f` with the subformula at `path` replaced by `at` applied to it.
     */
    def rewriteAt(f: Expression, path: List[Layer], at: Expression => Expression): Expression = (path, f) match
      case (Nil, _) => at(f)
      case (l :: rest, And(g, h)) if l.conj => if l.onLeft then and(rewriteAt(g, rest, at))(h) else and(g)(rewriteAt(h, rest, at))
      case (l :: rest, Or(g, h)) if !l.conj => if l.onLeft then or(rewriteAt(g, rest, at))(h) else or(g)(rewriteAt(h, rest, at))
      case _ => sys.error(s"prenex path does not match the formula at $f")

    /**
     * Lift `∀x. body` across the one connective `layer` that encloses it, at `pathToOuter` inside `src`.
     */
    def lift(srcIdx: Int, src: Expression, pathToOuter: List[Layer], layer: Layer, x: Variable, body: Expression): (Int, Expression) =
      val innerForall = forall(Lambda(x, body))
      // α-rename the binder away from the sibling's free variables, as `InstSchema` would, so the lifted
      // formula matches the law's instance.
      val (xL, bodyL) =
        if !layer.sibling.freeVariables.contains(x) then (x, body)
        else
          val xf = Variable(freshId(layer.sibling.freeVariables.view.map(_.id) ++ body.freeVariables.view.map(_.id), x.id), x.sort)
          (xf, substituteVariables(body, Map(x -> xf)))
      def join(a: Expression, b: Expression): Expression = if layer.conj then and(a)(b) else or(a)(b)
      // `lhsIff` keeps the original binder to match `src`.
      val (lhsIff, rhsIff) =
        if layer.onLeft then (join(innerForall, layer.sibling), forall(Lambda(xL, join(bodyL, layer.sibling))))
        else (join(layer.sibling, innerForall), forall(Lambda(xL, join(layer.sibling, bodyL))))
      val iff = lhsIff <=> rhsIff
      // `P := λx'. body'`, `R := sibling`.
      val iffIdx = emit(InstSchema(() |- iff, lawRef(layer), Map(schemaP -> Lambda(xL, bodyL), schemaR -> layer.sibling)))
      val lifted = rewriteAt(src, pathToOuter, _ => rhsIff)
      val hole = Variable(Identifier(GeneratedNames.hole, holes.next()), Prop)
      val substIdx = emit(RightSubstIff(Sequent(Set(iff), Set(lifted)), srcIdx, Seq((lhsIff, rhsIff)), (Seq(hole), rewriteAt(src, pathToOuter, _ => hole))))
      (emit(Cut(() |- lifted, iffIdx, substIdx, iff)), lifted)

    var refIdx = emit(Restate(() |- phi, -1))
    var current = phi
    // Lift the leftmost `∀` to the root one layer at a time, strip it there, and repeat.
    while locate(current).isDefined do
      var loc = locate(current).get
      while loc._1.nonEmpty do
        val (path, x, body) = loc
        val (idx, next) = lift(refIdx, current, path.init, path.last, x, body)
        refIdx = idx
        current = next
        loc = locate(current).get
      val (_, x, body) = loc
      val v = Variable(Identifier(GeneratedNames.clauseVar, counter.next()), Ind)
      val instantiated = substituteVariables(body, Map(x -> v))
      val hypIdx = emit(Hypothesis(instantiated |- instantiated, instantiated))
      val lfIdx = emit(LeftForall(current |- instantiated, hypIdx, body, x, v))
      refIdx = emit(Cut(() |- instantiated, refIdx, lfIdx, current))
      current = instantiated

    val innerImports = IndexedSeq(imported, forallAndLeftStatement, forallAndRightStatement, forallOrLeftStatement, forallOrRightStatement)
    val outerRefs = IndexedSeq(premise) ++
      Seq(libForallAndLeftIdx, libForallAndRightIdx, libForallOrLeftIdx, libForallOrRightIdx).map(libRef(nonLibSize, _))
    (SCSubproof(SCProof(steps.toIndexedSeq, innerImports), outerRefs), () |- current)
