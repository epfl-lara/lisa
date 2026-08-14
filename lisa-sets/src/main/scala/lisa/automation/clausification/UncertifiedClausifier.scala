package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

/**
 * The uncertified clausifier: an equisatisfiable clause set and no proof, for callers that need no certificate
 * (CASC, the benchmark harnesses). Vampire/E-style and a single pass rather than a chain of phases: selective
 * naming, NNF ([[NnfPhase.toNNF]]), one Skolemization descent directly producing fresh Skolem functions without ε-terms, and
 * distribution into clause sequents.
 *
 * [[CertifiedClausifier]] is the certified twin and `ClausifierEquivalenceTest` ensure that they make identical naming
 * decisions, and their Skolemized forms equal up to a renaming.
 *  ── top level: one formula → clauses (each a set of literals) ──────────────────────────────────
 */
object UncertifiedClausifier:

  /** Name a subformula once its CNF estimate exceeds this (clauses vs fresh-symbol trade-off; ~break-even at 4). */
  val DefaultThreshold: Int = 4

  // The three phases below are the halves of [[clausify]] exposed individually so the certified twin can be checked
  // against them stage by stage (`ClausifierEquivalenceTest`, via `CertifiedClausifier`'s oracle
  // block). `clausify` is this object's real entry point.

  /** The named formula (⇒ eliminated, blow-up subformulas replaced by fresh atoms), the naming half of [[clausify]]. */
  private[clausification] def namedFormula(phi: Expression, threshold: Int, counter: Counter): Expression =
    name(phi, 1, threshold, Set.empty, scala.collection.mutable.ListBuffer.empty[Expression], counter)._1

  /** The uncertified Skolemization of an NNF formula (∃ → Skolem functions, ∀ stripped). */
  private[clausification] def skolemizeNnf(nnf: Expression, counter: Counter): Expression =
    skolemize(nnf, Map.empty, Map.empty, nnf.freeVariables.iterator.filter(_.sort == Ind).map(v => (v, v)).toList, counter)

  /** The named formula (naming step) put through NNF and Skolemization. */
  private[clausification] def namedNnfSkolem(phi: Expression, threshold: Int): Expression =
    skolemizeNnf(NnfPhase.toNNF(namedFormula(phi, threshold, Counter()), negated = false), Counter())

  def clausify(phi: Expression, threshold: Int, frozen: Set[Variable], counter: Counter): List[Sequent] =
    val defs = scala.collection.mutable.ListBuffer.empty[Expression]
    val (named, _) = name(phi, 1, threshold, frozen, defs, counter)
    (named :: defs.toList).flatMap { g =>
      val nnf = NnfPhase.toNNF(g, negated = false)
      // Free Ind vars are the top-level universals, except the frozen ones, which are constants and so no
      // Skolem term's arguments. They aren't α-renamed, so orig = renamed.
      val univs = nnf.freeVariables.iterator.filter(v => v.sort == Ind && !frozen.contains(v)).map(v => (v, v)).toList
      toClauses(skolemize(nnf, Map.empty, Map.empty, univs, counter))
    }

  /** The hypotheses to clausify, `problem`'s own plus the negated conjecture, and the variables the prover must
   *  treat as symbols rather than clause variables: `problem.frozen` plus the conjecture's free individual
   *  variables, which are frozen for the reason [[NegatedPhase]] gives. */
  private def negated(problem: Problem): (IndexedSeq[Sequent], Set[Variable]) =
    problem.conjecture match
      case None => (problem.hypotheses.toIndexedSeq, problem.frozen)
      case Some(c) =>
        val phi = singleRightFormula(c, "conjecture")
        (problem.hypotheses.toIndexedSeq :+ (() |- neg(phi)), problem.frozen ++ phi.freeVariables.filter(_.sort == Ind))

  /** Clausal form of `problem`. The conjecture is negated and appended as the last hypothesis, as
   *  [[NegatedPhase]] does, but the rest is the single-pass pipeline. */
  def clausalForm(problem: Problem, threshold: Int = DefaultThreshold, orthologic: Boolean = false): Problem =
    Problem(clausalFormWithOrigins(problem, threshold, orthologic).map(_._1).toList, None, negated(problem)._2)

  /** Pairs each clause with the index of the source formula it was clausified from:
   *  an index into `hypotheses ++ [¬conjecture]. Lets a proof-printing front-end attribute every clause to its single origin axiom. */
  def clausalFormWithOrigins(problem: Problem, threshold: Int = DefaultThreshold, orthologic: Boolean = false): IndexedSeq[(Sequent, Int)] =
    val (hyps0, frozen) = negated(problem)
    val counter = Counter(freshCounterStart(hyps0))
    hyps0.zipWithIndex.flatMap { (h, origin) =>
      val f0 = singleRightFormula(h, "hypothesis")
      // η-expand after the orthologic step, because `reducedNNFForm` produces an eta-contracted formula
      val f  = etaExpandQuantifiers(if orthologic then reducedNNFForm(f0) else f0)
      clausify(f, threshold, frozen, counter).map(clause => (clause, origin))
    }

  /**
   * Where the shared fresh-name counter must start so that nothing this path mints collides with an input name.
   * The three generated kinds (`w` clause variables, `sk` Skolem functions, `nm` naming atoms) share one
   * counter.
   */
  private def freshCounterStart(hypotheses: Seq[Sequent]): Int =
    val prefixes = Set(GeneratedNames.clauseVar, GeneratedNames.uncertifiedSkolem, GeneratedNames.namingAtom)
    var maxNo = -1
    def note(id: Identifier): Unit = if prefixes(id.name) && id.no > maxNo then maxNo = id.no
    def scan(e: Expression): Unit = e match
      case Application(f, a) => scan(f); scan(a)
      case Lambda(v, b)      => note(v.id); scan(b)
      case v: Variable       => note(v.id)
      case c: Constant       => note(c.id)
    hypotheses.foreach(s => { s.left.foreach(scan); s.right.foreach(scan) })
    maxNo + 1

  // ── selective naming ─────────────────────────────────────────────────────────────────────────────────────

  // Introduce a fresh atom for `c` (occurring at polarity `pol`) + its directional definition; returns the atom.
  private def define(c: Expression, pol: Int, frozen: Set[Variable], defs: scala.collection.mutable.ListBuffer[Expression], counter: Counter): Expression =
    val (_, _, atom) = NamingSupport.freshNamingAtom(c, counter, frozen)
    defs +=
      (if pol > 0 then or(neg(atom))(c) //            positive occurrence: d ⇒ c
       else if pol < 0 then or(atom)(neg(c)) //       negative occurrence: c ⇒ d
       else and(or(neg(atom))(c))(or(atom)(neg(c)))) // both (under ⇔):     d ⟺ c
    atom

  private inline def relevantBig(e: Est, pol: Int, threshold: Int): Boolean =
    if pol > 0 then e.pos > threshold else if pol < 0 then e.neg > threshold else e.pos > threshold || e.neg > threshold

  /** Rewrite `f` (at polarity `pol`) naming a subformula in multiplicative context; return the rewritten
   *  formula and its clause-count estimate. Single bottom-up pass: each node's estimate is combined from
   *  its (already-processed) children's, never recomputed. */
  private def name(f: Expression, pol: Int, threshold: Int, frozen: Set[Variable], defs: scala.collection.mutable.ListBuffer[Expression], counter: Counter): (Expression, Est) =
    f match
      case And(g, h) => // pos = Σ (additive), neg = Π (multiplicative)
        var (g2, eg) = name(g, pol, threshold, frozen, defs, counter)
        var (h2, eh) = name(h, pol, threshold, frozen, defs, counter)
        while pol <= 0 && capMul(eg.neg, eh.neg) > threshold && (eg.neg > 1 || eh.neg > 1) do
          if eg.neg >= eh.neg && eg.neg > 1 then { g2 = define(g2, pol, frozen, defs, counter); eg = atomEst }
          else { h2 = define(h2, pol, frozen, defs, counter); eh = atomEst }
        (and(g2)(h2), Est.and(eg, eh))
      case Or(g, h) => // pos = Π (multiplicative), neg = Σ (additive)
        var (g2, eg) = name(g, pol, threshold, frozen, defs, counter)
        var (h2, eh) = name(h, pol, threshold, frozen, defs, counter)
        while pol >= 0 && capMul(eg.pos, eh.pos) > threshold && (eg.pos > 1 || eh.pos > 1) do
          if eg.pos >= eh.pos && eg.pos > 1 then { g2 = define(g2, pol, frozen, defs, counter); eg = atomEst }
          else { h2 = define(h2, pol, frozen, defs, counter); eh = atomEst }
        (or(g2)(h2), Est.or(eg, eh))
      case Neg(g) =>
        val (g2, eg) = name(g, -pol, threshold, frozen, defs, counter)
        (neg(g2), Est.neg(eg))
      case Implies(g, h) => name(or(neg(g))(h), pol, threshold, frozen, defs, counter) // eliminate → to ¬g ∨ h
      case Iff(g, h) => // children live at both polarities; both pos and neg are multiplicative
        var (g2, eg) = name(g, 0, threshold, frozen, defs, counter)
        var (h2, eh) = name(h, 0, threshold, frozen, defs, counter)
        while relevantBig(Est.iff(eg, eh), pol, threshold) && (Est.size(eg) > 2 || Est.size(eh) > 2) do
          if Est.size(eg) >= Est.size(eh) && Est.size(eg) > 2 then { g2 = define(g2, 0, frozen, defs, counter); eg = atomEst }
          else { h2 = define(h2, 0, frozen, defs, counter); eh = atomEst }
        (g2 <=> h2, Est.iff(eg, eh))
      case Forall(x, g) => val (g2, eg) = name(g, pol, threshold, frozen, defs, counter); (forall(x, g2), eg)
      case Exists(x, g) => val (g2, eg) = name(g, pol, threshold, frozen, defs, counter); (exists(x, g2), eg)
      case `top`        => (top, Est(0, 1))
      case `bot`        => (bot, Est(1, 0))
      case atom         => (atom, atomEst)

  // ── single-pass Skolemization (fresh Skolem functions; strip ∀; α-rename) ───────────────────────

  // `univs` pairs each in-scope universal's ORIGINAL bound variable with its α-renamed clause variable (used in the
  // Skolem term). Each ∃ gets its **own** fresh Skolem symbol; we do NOT dedup syntactically-identical existentials.
  // `imageFree` records the free variables of each `subst` image, so the ∃ case below needs no substituted copy.
  private def skolemize(f: Expression, subst: Map[Variable, Expression], imageFree: Map[Variable, Set[Variable]],
                        univs: List[(Variable, Variable)], counter: Counter): Expression =
    f match
      case And(g, h) => and(skolemize(g, subst, imageFree, univs, counter))(skolemize(h, subst, imageFree, univs, counter))
      case Or(g, h)  => or(skolemize(g, subst, imageFree, univs, counter))(skolemize(h, subst, imageFree, univs, counter))
      case Forall(x, g) => // α-rename to a fresh var (avoid capture), strip the ∀, extend the universal context
        val v = Variable(Identifier(GeneratedNames.clauseVar, counter.next()), x.sort)
        skolemize(g, subst + (x -> v), imageFree + (x -> Set(v)), if x.sort == Ind then univs :+ (x, v) else univs, counter)
      case Exists(x, g) => // fresh Skolem function over ONLY the universals the witness can depend on,
        // including transitive dependencies on a universal `u` that reach the body only through an earlier
        // ∃-variable's Skolem term. So the set wanted is the free variables of the body *after* `subst`, which is
        // `⋃ FV(subst y)` over the `y` free in `f`: no substituted copy is built, each image's free variables
        // being known when it is inserted (`{v}` for a stripped ∀, the argument list for a Skolem term).
        val bodyFree = f.freeVariables.flatMap(y => imageFree.getOrElse(y, Set(y)))
        val mentioned = univs.collect { case (_, v) if bodyFree.contains(v) => v }
        val skSort = mentioned.foldRight(x.sort)((u, acc) => u.sort -> acc)
        // A **Constant** (function symbol), NOT a Variable: a *nullary* Skolem has result sort `Ind`, so as a
        // Variable it would be mistaken for a clause variable (universally quantified), which is unsound.
        val skTerm = mentioned.foldLeft(Constant(Identifier(GeneratedNames.uncertifiedSkolem, counter.next()), skSort): Expression)((acc, u) => acc(u))
        skolemize(g, subst + (x -> skTerm), imageFree + (x -> mentioned.toSet), univs, counter)
      case lit => if subst.isEmpty then lit else substituteVariablesOpti(lit, subst)

  // ── distribution to clauses ─────────────────────────────────────────────────────────────────────

  /** The clauses of a quantifier-free NNF matrix, each as `a₁, …, aₘ ⊢ b₁, …, bₙ` (README §1.4). The two sides
   *  are separated at the leaves, as [[DistributePhase.distributeClauses]] does on the certified side. */
  private def toClauses(f: Expression): List[Sequent] =
    f match
      case And(g, h) => toClauses(g) ++ toClauses(h)
      case Or(g, h)  => val cg = toClauses(g); val ch = toClauses(h)
                        for a <- cg; b <- ch yield Sequent(a.left ++ b.left, a.right ++ b.right)
      case `top`     => Nil //                                  ⊤ conjunct contributes no clause
      case `bot`     => List(Sequent(Set.empty, Set.empty)) //   ⊥ conjunct is the empty clause
      case Neg(atom) => List(Sequent(Set(atom), Set.empty)) //   a negative literal is its atom, on the left
      case lit       => List(Sequent(Set.empty, Set(lit)))

  // ── the prover-facing entry point ───────────────────────────────────────────────────────────────

  /**
   * Compute the clausal form and hand it to `prover`, returning the prover's proof verbatim (imports = the
   * clauses, conclusion `∅ ⊢`). The same signature as [[CertifiedClausifier.certifyClausal]], so a caller can
   * swap one for the other, but the clausification is **not** certified: nothing links the clauses back to the
   * original conjecture, and the returned proof refutes the clause set only.
   */
  def uncertifyClausal(problem: Problem, prover: Problem => SCProof): SCProof =
    prover(clausalForm(problem))
