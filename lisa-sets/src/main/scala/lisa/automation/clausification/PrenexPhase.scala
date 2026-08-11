package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * Universal-quantifier stripping. After [[SkolemPhase]] the only quantifier left is `∀`, and a clause carries no
 * quantifiers at all — its variables are implicitly universal. So this phase replaces each `∀x. …` by its body
 * with `x` instantiated at a fresh clause variable `w`, leaving [[DistributePhase]] a quantifier-free matrix.
 *
 * The quantifiers are *not* necessarily at the root: NNF leaves them wherever they sat in the input, so `∀` can
 * appear under `∧`/`∨`/`¬` anywhere in the tree. Two strategies handle that, both producing `() ⊢ matrix` from
 * the imported `() ⊢ φ`, and [[preferRewriteStrategy]] picks between them per formula:
 *
 *   - [[provePrenexDeconstruct]] walks `φ`'s tree and applies `LeftForall` at each `∀` node where it stands.
 *     Proof size linear in `|φ|`, so it wins whenever the formula is small relative to its quantifier count.
 *   - [[provePrenexRewrite]] first lifts each `∀` to the root one connective at a time, using the four
 *     `forall{And,Or}{Left,Right}` library laws ([[Clausification.libImports]]), then strips at the root.
 *     Size ~`nq × depth`, so it wins on a large formula with few quantifiers.
 *
 * '''Both must agree on the witnesses.''' [[extractUniversalMatrix]] computes the matrix and mints the `w`s in
 * pre-order, and each strategy has to reproduce *that* matrix exactly; `provePrenex` asserts it. This is why the
 * rewrite path α-renames a binder before lifting it over a sibling — the kernel's `InstSchema` substitutes
 * capture-avoidingly, so a hand-built formula that captured would silently disagree with the one the kernel
 * derives, and the mismatch would only surface at the closing `require`.
 *
 * A formula with no `∀` anywhere is passed through untouched ([[hasForall]] is the gate). Note that `hasForall`
 * cannot see an η-reduced `∀(p)`, which is why [[ScreenPhase]] η-expands every quantifier before this runs.
 */
private[clausification] object PrenexPhase:

  /** For each axiom containing a `∀` anywhere in its tree, strip all universals — instantiating each at a fresh
    * clause variable `w` (pre-order) via `LeftForall`. Certifies the derivation of the quantifier-free matrix
    * via [[provePrenex]]. */
  def certifyPrenex(problem: Problem, prover: ClausificationProver): ClausificationProof = {
    certifyAxiomwise(problem, prover, (ax, counter, ctx) => {
      val phi = singleRightFormula(ax, "axiom")
      if !hasForall(phi) then None
      else
        // Outer step 0 derives matrixAx from ax via universal-quantifier stripping,
        // using `witnesses` (the fresh clause variables `w` introduced by [[extractUniversalMatrix]]
        // in pre-order) as instantiation terms.
        val (matrix, witnesses) = extractUniversalMatrix(phi, counter)
        val matrixAx   = () |- matrix
        // Lib refs in the outer ClausificationProof (ax :: rest ++ done ++ libImports).
        val prenexLibRefs = (
          libRef(ctx.nonLibSize, libForallAndLeftIdx),
          libRef(ctx.nonLibSize, libForallAndRightIdx),
          libRef(ctx.nonLibSize, libForallOrLeftIdx),
          libRef(ctx.nonLibSize, libForallOrRightIdx)
        )
        val prenexStep = KernelStep(provePrenex(ax, -1, matrixAx, witnesses, prenexLibRefs))
        Some((matrixAx, IndexedSeq(prenexStep), 0))
    })
  }

  /**
    * Build a subproof of `() ⊢ matrix` from the imported `() ⊢ phi`, where `phi`
    * may contain `∀`-quantifiers *anywhere* in the tree (not necessarily at the root).
    * `matrix` is `phi` with every `∀x._` stripped and `x` replaced by the
    * corresponding fresh clause variable `w` (pre-order, as computed by [[extractUniversalMatrix]]).
    *
    * Two strategies, dispatched by [[preferRewriteStrategy]]:
    *   - [[provePrenexDeconstruct]]: walk `phi`'s tree, apply `LeftForall` at each
    *     `∀` node in-place. O(|phi|).
    *   - [[provePrenexRewrite]]: lift each `∀` to the root one connective at a time
    *     via prenex-equivalence rewrites, then strip with `LeftForall`. O(nq × depth).
    *
    * @param forceRewrite take the rewrite branch whatever the heuristic says. Only `PrenexRewriteTest` passes
    *                     it: the heuristic picks `deconstruct` for most shapes, so the rewrite path would go
    *                     largely unexercised otherwise. There is deliberately no matching `forceDeconstruct`
    *                     — it existed, nothing ever set it, and a knob no caller uses is a knob that is not
    *                     known to work. */
  def provePrenex(
      imported: Sequent,
      premise: Int,
      conclusion: Sequent,
      witnesses: Seq[Variable],
      libPrenexRefs: (Int, Int, Int, Int),
      forceRewrite: Boolean = false
  ): SCSubproof = {
    val phi = singleRightFormula(imported, "imported (prenex source)")
    if (forceRewrite || preferRewriteStrategy(phi))
      provePrenexRewrite(imported, premise, conclusion, witnesses, libPrenexRefs)
    else provePrenexDeconstruct(imported, premise, conclusion, witnesses)
  }

  def hasForall(f: Expression): Boolean = f match
    case Forall(_, _) => true
    case And(g, h)    => hasForall(g) || hasForall(h)
    case Or(g, h)     => hasForall(g) || hasForall(h)
    case Neg(g)       => hasForall(g)
    case _            => false

  /** Per-formula heuristic deciding between the rewrite and deconstruction prenex
    * strategies.  Returns `true` if [[provePrenexRewrite]] is expected to produce
    * a smaller proof than [[provePrenexDeconstruct]].
    *
    * Currently a coarse global heuristic: pick rewriting when the formula has
    * many leaves but few quantifiers, deconstruction otherwise. */
  def preferRewriteStrategy(phi: Expression): Boolean = {
    def counts(e: Expression): (Int, Int) = e match // (size, numForall)
      case Forall(_, body) =>
        val (s, q) = counts(body); (s + 1, q + 1)
      case And(g, h) =>
        val (sg, qg) = counts(g); val (sh, qh) = counts(h)
        (sg + sh + 1, qg + qh)
      case Or(g, h) =>
        val (sg, qg) = counts(g); val (sh, qh) = counts(h)
        (sg + sh + 1, qg + qh)
      case Neg(body) =>
        val (s, q) = counts(body); (s + 1, q)
      case _ => (1, 0)
    val (size, nq) = counts(phi)
    // rewrite cost ~nq·depth vs deconstruction ~size; cross over near size ≈ nq²
    nq > 0 && size > 4 * nq * nq
  }

  /** Deconstruction strategy: build a kernel proof of `phi ⊢ matrix` by walking
    * `phi`'s tree, mirroring its connectives, and using `LeftForall` directly to
    * instantiate each universal at its corresponding witness from `witnesses`
    * (pre-order). Then `Cut` against `imported` to obtain `() ⊢ matrix`.
    *
    * Proof size is linear in `|phi|`. */
  private def provePrenexDeconstruct(
      imported: Sequent,
      premise: Int,
      conclusion: Sequent,
      witnesses: Seq[Variable]
  ): SCSubproof = {
    val phi    = singleRightFormula(imported, "imported (prenex source)")
    val matrix = singleRightFormula(conclusion, "conclusion (prenex matrix)")

    val steps = scala.collection.mutable.ArrayBuffer.empty[SCProofStep]
    def emit(s: SCProofStep): Int = { steps += s; steps.size - 1 }

    val witsIter = witnesses.iterator

    // Builds steps with conclusion `orig ⊢ matrixOf(orig)` and returns the step index.
    // Fast path: if `orig` contains no ∀, its matrix is itself — no tree walk needed.
    def go(orig: Expression): Int =
      if !hasForall(orig) then emit(Hypothesis(orig |- orig, orig))
      else orig match
      case Forall(x, body) =>
        require(witsIter.hasNext, "Witness list exhausted while walking universals")
        val v = witsIter.next()
        val bodySub  = substituteVariablesOpti(body, Map(x -> v))
        val innerIdx = go(bodySub)
        val innerM   = steps(innerIdx).bot.right.head
        // LeftForall(b, t1, phi, x, t): from `Γ, body[x:=v] ⊢ Δ` derive `Γ, ∀x.body ⊢ Δ`.
        emit(LeftForall(orig |- innerM, innerIdx, body, x, v))

      case And(g, h) =>
        val gIdx = go(g)
        val hIdx = go(h)
        val mg = steps(gIdx).bot.right.head
        val mh = steps(hIdx).bot.right.head
        val mAnd = and(mg)(mh)
        val gWithAnd = emit(LeftAnd(orig |- mg, gIdx, g, h))
        val hWithAnd = emit(LeftAnd(orig |- mh, hIdx, g, h))
        emit(RightAnd(orig |- mAnd, Seq(gWithAnd, hWithAnd), Seq(mg, mh)))

      case Or(g, h) =>
        val gIdx = go(g)
        val hIdx = go(h)
        val mg = steps(gIdx).bot.right.head
        val mh = steps(hIdx).bot.right.head
        val mOr = or(mg)(mh)
        // RightOr lifts each branch to the disjunctive matrix; LeftOr combines them.
        val gWithOr = emit(RightOr(g |- mOr, gIdx, mg, mh))
        val hWithOr = emit(RightOr(h |- mOr, hIdx, mg, mh))
        emit(LeftOr(orig |- mOr, Seq(gWithOr, hWithOr), Seq(g, h)))

      case _ =>
        // NNF leaves: atoms and negated atoms — Hypothesis suffices.
        emit(Hypothesis(orig |- orig, orig))

    val phiToMatrixIdx = go(phi)
    require(steps(phiToMatrixIdx).bot.right.head == matrix,
      s"Deconstruction produced unexpected matrix: got ${steps(phiToMatrixIdx).bot.right.head}, expected $matrix")
    require(!witsIter.hasNext, "Unused witnesses after walking universals")
    // Cut: from `() ⊢ phi` (import 0) and `phi ⊢ matrix` derive `() ⊢ matrix`.
    emit(Cut(() |- matrix, -1, phiToMatrixIdx, phi))

    SCSubproof(SCProof(steps.toIndexedSeq, IndexedSeq(imported)), IndexedSeq(premise))
  }

  /** Description of a single one-layer step lifting `∀x.body` across the
    * surrounding connective when it sits inside `(…) ⊕ Q` or `Q ⊕ (…)`. */
  sealed trait LiftLayer
  case class LayerAndL(rhs: Expression) extends LiftLayer  // (∀x.body) ∧ rhs  →  ∀x.(body ∧ rhs)
  case class LayerAndR(lhs: Expression) extends LiftLayer  // lhs ∧ (∀x.body)  →  ∀x.(lhs ∧ body)
  case class LayerOrL (rhs: Expression) extends LiftLayer  // (∀x.body) ∨ rhs  →  ∀x.(body ∨ rhs)
  case class LayerOrR (lhs: Expression) extends LiftLayer  // lhs ∨ (∀x.body)  →  ∀x.(lhs ∨ body)

  /** Rewriting strategy: for each universal quantifier in `phi` (in pre-order), lift it to the top of the
    * formula via `RightSubstIff` with the appropriate prenex equivalence (proven inline), then strip it with
    * `LeftForall` at the matching witness from `witnesses`. After all quantifiers are stripped we have
    * `() ⊢ matrix`; the remaining body's structure is never destructured. Cost per quantifier: `O(nb_q*depth)`
    * rewrites (one per enclosing connective on the path from root to the quantifier). */
  private def provePrenexRewrite(
      imported: Sequent,
      premise: Int,
      conclusion: Sequent,
      witnesses: Seq[Variable],
      libPrenexRefs: (Int, Int, Int, Int)
  ): SCSubproof = {
    val phi    = singleRightFormula(imported, "imported (prenex source)")
    val matrix = singleRightFormula(conclusion, "conclusion (prenex matrix)")
    val (outerLibAndL, outerLibAndR, outerLibOrL, outerLibOrR) = libPrenexRefs
    // Inside the inner SCProof, the prenex-lifting library theorems appear as
    // imports 1..4 (0-based), referenced as -2 through -5.
    val innerLibAndL = -2; val innerLibAndR = -3
    val innerLibOrL  = -4; val innerLibOrR  = -5

    val steps = scala.collection.mutable.ArrayBuffer.empty[SCProofStep]
    def emit(s: SCProofStep): Int = { steps += s; steps.size - 1 }
    val freshCounter = Counter()

    // Locate the leftmost ∀ in pre-order.  Returns the path (root→quantifier) of
    // one-layer descents, plus the bound variable and body of the ∀ found.
    def locateForall(f: Expression): Option[(List[LiftLayer], Variable, Expression)] = f match
      case Forall(x, body) => Some((Nil, x, body))
      case And(g, h) =>
        locateForall(g).map { case (p, x, b) => (LayerAndL(h) :: p, x, b) }
          .orElse(locateForall(h).map { case (p, x, b) => (LayerAndR(g) :: p, x, b) })
      case Or(g, h) =>
        locateForall(g).map { case (p, x, b) => (LayerOrL(h) :: p, x, b) }
          .orElse(locateForall(h).map { case (p, x, b) => (LayerOrR(g) :: p, x, b) })
      case _ => None

    /** Replace the sub-expression at `path` (relative to root of `f`) using `f0 => f1`. */
    def rewriteAt(f: Expression, path: List[LiftLayer], at: Expression => Expression): Expression =
      path match
        case Nil => at(f)
        case LayerAndL(_) :: rest => f match { case And(g, h) => and(rewriteAt(g, rest, at))(h); case _ => sys.error("path mismatch (∧L)") }
        case LayerAndR(_) :: rest => f match { case And(g, h) => and(g)(rewriteAt(h, rest, at)); case _ => sys.error("path mismatch (∧R)") }
        case LayerOrL(_)  :: rest => f match { case Or(g, h)  => or(rewriteAt(g, rest, at))(h);  case _ => sys.error("path mismatch (∨L)") }
        case LayerOrR(_)  :: rest => f match { case Or(g, h)  => or(g)(rewriteAt(h, rest, at));  case _ => sys.error("path mismatch (∨R)") }

    /** Sub-expression at `path` in `f`. */
    def subAt(f: Expression, path: List[LiftLayer]): Expression =
      path match
        case Nil => f
        case LayerAndL(_) :: rest => f match { case And(g, _) => subAt(g, rest); case _ => sys.error("path mismatch (∧L)") }
        case LayerAndR(_) :: rest => f match { case And(_, h) => subAt(h, rest); case _ => sys.error("path mismatch (∧R)") }
        case LayerOrL(_)  :: rest => f match { case Or(g, _)  => subAt(g, rest); case _ => sys.error("path mismatch (∨L)") }
        case LayerOrR(_)  :: rest => f match { case Or(_, h)  => subAt(h, rest); case _ => sys.error("path mismatch (∨R)") }

    /** Apply one prenex equivalence at `pathToInner` (whose tail describes the
      * single connective layer to cross) inside `srcFormula`, producing a step
      * whose conclusion is `() ⊢ liftedFormula`. */
    def liftOneLayer(
        srcIdx: Int,
        srcFormula: Expression,
        pathToOuter: List[LiftLayer],   // path from root to the ⊕-node containing ∀x.body
        layer: LiftLayer,               // describes which side of ⊕ holds the ∀
        x: Variable,
        body: Expression
    ): (Int, Expression) = {
      val innerForall = forall(Lambda(x, body))
      // The `⊕`-node's other operand, and the library law for this layer.
      val (sibling, libRef): (Expression, Int) = layer match
        case LayerAndL(rhs) => (rhs, innerLibAndL)
        case LayerAndR(lhs) => (lhs, innerLibAndR)
        case LayerOrL(rhs)  => (rhs, innerLibOrL)
        case LayerOrR(lhs)  => (lhs, innerLibOrR)

      // α-rename the binder away from the sibling before lifting over it: `(∀x. body) ⊕ s` lifts to
      // `∀x'. (body[x:=x'] ⊕ s)` with `x'` fresh for `s`. Reusing `x` would *capture* a free `x` in `s`, and the
      // result would not be an instance of the law — which holds only because `R` is a nullary `Prop` schema and
      // so cannot contain the bound variable at all.
      //
      // The rename must be done by hand here and cannot be left to the kernel: `InstSchema` substitutes
      // `schemaR := s` capture-*avoidingly*, so it produces the renamed formula regardless, and a hand-built
      // `rhsIff` that captured would disagree with it. The strip at the end would then yield a matrix
      // `extractUniversalMatrix` never predicted, failing `provePrenex`'s closing `require`.
      val (xL, bodyL): (Variable, Expression) =
        if !sibling.freeVariables.contains(x) then (x, body)
        else
          val xf = Variable(freshId(sibling.freeVariables.view.map(_.id) ++ body.freeVariables.view.map(_.id), x.id), x.sort)
          (xf, substituteVariables(body, Map(x -> xf)))

      // `lhsIff` must match the node as it stands in `srcFormula`, so it keeps the original binder; only the
      // lifted side uses the renamed one.
      val (lhsIff, rhsIff): (Expression, Expression) = layer match
        case LayerAndL(_) => (and(innerForall)(sibling), forall(Lambda(xL, and(bodyL)(sibling))))
        case LayerAndR(_) => (and(sibling)(innerForall), forall(Lambda(xL, and(sibling)(bodyL))))
        case LayerOrL(_)  => (or(innerForall)(sibling),  forall(Lambda(xL, or(bodyL)(sibling))))
        case LayerOrR(_)  => (or(sibling)(innerForall),  forall(Lambda(xL, or(sibling)(bodyL))))

      val iffFormula = lhsIff <=> rhsIff
      // Instantiate the prenex library theorem to get `() ⊢ iffFormula`. `schemaP := λx'.body'` is the quantified
      // side; `schemaR := sibling` is the closed side, supplied unwrapped since `R` is nullary `Prop`. Both sides
      // of the substituted statement are α-equivalent to `iffFormula`'s (the statement's own binder may be
      // renamed by the same capture-avoidance, which `InstSchema` compares up to), so the step checks.
      val schemaSubst: Map[Variable, Expression] = Map(schemaP -> Lambda(xL, bodyL), schemaR -> sibling)
      val iffStep = emit(InstSchema(() |- iffFormula, libRef, schemaSubst))

      // Lifted formula: replace `lhsIff` at `pathToOuter` with `rhsIff`.
      val liftedFormula = rewriteAt(srcFormula, pathToOuter, _ => rhsIff)

      // Build the context lambda for RightSubstIff: λp. srcFormula[pathToOuter := p].
      val pVar = Variable(Identifier(GeneratedNames.hole, freshCounter.next()), Prop)
      val ctxBody = rewriteAt(srcFormula, pathToOuter, _ => pVar)

      val substStep = emit(RightSubstIff(
        Sequent(Set(iffFormula), Set(liftedFormula)),
        srcIdx,
        Seq((lhsIff, rhsIff)),
        (Seq(pVar), ctxBody)
      ))
      val cutStep = emit(Cut(() |- liftedFormula, iffStep, substStep, iffFormula))
      (cutStep, liftedFormula)
    }

    // Start by Restating `imported` to obtain `() ⊢ phi` at a known index.
    var currentRefIdx = emit(Restate(() |- phi, -1))
    var currentFormula: Expression = phi
    val witsIter = witnesses.iterator

    // Outer loop: lift one ∀ to the root, then strip it; repeat until no ∀ remains.
    while locateForall(currentFormula).isDefined do
      // Inner loop: while the located ∀ is below the root, lift it one layer.
      var loc = locateForall(currentFormula).get
      while loc._1.nonEmpty do
        val (path, x, body) = loc
        // The ∀-containing ⊕-node is at `path.init`; the final step describes
        // which side the ∀ sits on (and what the sibling is).
        val pathToOuter = path.init
        val finalLayer  = path.last
        val (newIdx, newFormula) = liftOneLayer(currentRefIdx, currentFormula, pathToOuter, finalLayer, x, body)
        currentRefIdx = newIdx
        currentFormula = newFormula
        loc = locateForall(currentFormula).get
      // ∀ is now at the root: strip it.
      require(witsIter.hasNext, "Encountered top-level ∀ but no witness to instantiate")
      val v = witsIter.next()
      val (_, x, body) = loc
      val instantiated = substituteVariables(body, Map(x -> v))
      val hypIdx = emit(Hypothesis(instantiated |- instantiated, instantiated))
      val lfIdx  = emit(LeftForall(currentFormula |- instantiated, hypIdx, body, x, v))
      val cutIdx = emit(Cut(() |- instantiated, currentRefIdx, lfIdx, currentFormula))
      currentRefIdx = cutIdx
      currentFormula = instantiated

    require(!witsIter.hasNext, "Witnesses left over with no ∀ to instantiate")
    require(currentFormula == matrix,
      s"Rewrite produced unexpected matrix: got $currentFormula, expected $matrix")

    // Inner SCProof imports: 0 = `imported` (the source axiom), 1..4 = prenex lib theorems.
    val innerImports = IndexedSeq(imported, forallAndLeftStatement, forallAndRightStatement, forallOrLeftStatement, forallOrRightStatement)
    SCSubproof(
      SCProof(steps.toIndexedSeq, innerImports),
      IndexedSeq(premise, outerLibAndL, outerLibAndR, outerLibOrL, outerLibOrR)
    )
  }

  def extractUniversalMatrix(f: Expression, counter: Counter): (Expression, Seq[Variable]) = {
    def go(f: Expression, subst: Map[Variable, Expression]): (Expression, Seq[Variable]) =
      f match
        case Forall(x, inner) =>
          val fresh = Variable(Identifier(GeneratedNames.clauseVar, counter.next()), Ind)
          val (matrix, vars) = go(inner, subst + (x -> fresh))
          (matrix, fresh +: vars)
        case And(left, right) =>
          val (leftMatrix, leftVars) = go(left, subst)
          val (rightMatrix, rightVars) = go(right, subst)
          (and(leftMatrix)(rightMatrix), leftVars ++ rightVars)
        case Or(left, right) =>
          val (leftMatrix, leftVars) = go(left, subst)
          val (rightMatrix, rightVars) = go(right, subst)
          (or(leftMatrix)(rightMatrix), leftVars ++ rightVars)
        case Neg(inner) =>
          val (innerMatrix, innerVars) = go(inner, subst)
          (neg(innerMatrix), innerVars)
        case other =>
          (substituteVariablesOpti(other, subst), Seq.empty)
    go(f, Map.empty)
  }
