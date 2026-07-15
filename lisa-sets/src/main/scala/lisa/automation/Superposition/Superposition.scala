package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.IntArrayList

import Core.*
import Cmp.*

/**
 * The generating equality inferences of the superposition calculus (Phase 4): **superposition**,
 * **equality resolution**, and **equality factoring**. Equality resolution/factoring mirror the
 * [[Inference.resolve]] / `factor` idiom: save the trail, unify (one scope), apply the post-σ ordering
 * gates against the shared [[Order]]'s KBO, build the conclusion via a [[Trail.Applier]], restore the
 * trail. **Superposition splits this**: because the overlap is *located and unified by the caller* (the
 * saturation loop, or the term index in Phase 5 — as Vampire's index feeds a substitution to
 * `performSuperposition`), [[superpose]] receives a trail **already bearing** `mgu(l, u)` and only gates
 * and builds; the caller owns the surrounding `save` / `unify` / `restore`.
 *
 * **Eligibility (literal selection / maximality) is the loop's concern, not these functions'.** With a
 * Bachmair-Ganzinger selection function a *selected* negative literal is eligible even when it is not
 * maximal, so an `isMaximal` gate inside the inference would wrongly block it and lose completeness. The
 * loop (Step 4) therefore passes only the literal positions taken from each clause's `selected` set, and
 * these functions enforce only the **term-orientation** conditions, which are required for completeness
 * and independent of selection. (The post-σ maximality *aftercheck* -- a redundancy pruning -- is a
 * deferred optimisation; omitting it over-approximates, which is sound and complete.)
 *
 * Subterm positions are paths of argument indices into a literal's atom (root excluded, length ≥ 1);
 * superposition never rewrites into a variable nor into the atom root.
 */
object Superposition:

  // --- position helpers --------------------------------------------------------------------------
  //
  // A subterm position is a path of argument indices into an atom (root excluded), represented as
  // `Array[Int]`. It is only *materialised* when an inference fires and must record it in a
  // `Justification`; enumeration itself ([[foreachSubterm]]) walks a single **reused** mutable stack, so
  // it allocates nothing per position — the E/Vampire subterm-iterator style.

  /** The subterm of `t` at position `pos` (a path of argument indices). */
  def subtermAt(bank: TermBank, t: Term, pos: Array[Int]): Term =
    var cur: Term = t
    var i = 0
    while i < pos.length do { cur = bank.arg(cur, pos(i)); i += 1 }
    cur

  /** Rebuild `t` with the subterm at position `pos` replaced by `sub`. */
  def replaceAt(bank: TermBank, t: Term, pos: Array[Int], sub: Term): Term = replaceAt(bank, t, pos, 0, sub)

  private def replaceAt(bank: TermBank, t: Term, pos: Array[Int], depth: Int, sub: Term): Term =
    if depth == pos.length then sub
    else
      val k: Int = pos(depth)
      val n: Int = bank.arity(t)
      val args: Array[Term] = new Array[Term](n)
      var i = 0
      while i < n do
        args(i) = if i == k then replaceAt(bank, bank.arg(t, k), pos, depth + 1, sub) else bank.arg(t, i)
        i += 1
      bank.mkApp(bank.headSymbol(t), args)

  /**
   * Visit every **non-variable** proper subterm of `atom` (root excluded), leftmost-outermost, calling
   * `visit(u, path)` with the subterm `u` and its current position. The `path` [[IntArrayList]] is a single
   * stack **reused** across the whole traversal (pushed on descent, popped on return), so enumeration
   * allocates nothing per position. Snapshot it (`path.toIntArray`) inside `visit` **only** when you keep
   * the position, i.e. when an inference actually fires. `visit` returns `true` to stop the traversal
   * early; `foreachSubterm` then returns `true` (some visit stopped it), else `false`.
   */
  def foreachSubterm(bank: TermBank, atom: Term)(visit: (Term, IntArrayList) => Boolean): Boolean =
    val path: IntArrayList = new IntArrayList()
    def go(t: Term): Boolean =
      val n: Int = bank.arity(t)
      var i = 0
      while i < n do
        val a: Term = bank.arg(t, i)
        if !bank.isVar(a) then
          path.push(i)
          if visit(a, path) then return true
          if go(a) then return true
          path.popInt()
        i += 1
      false
    go(atom)

  // --- inference rules ---------------------------------------------------------------------------

  /** Whether `c` is `Gt` or `Eq` (i.e. `a ≽ b` when `c = compare(a, b)`). */
  private inline def geq(c: Cmp): Boolean = c == Gt || c == Eq

  /**
   * **Superposition** (build only). The trail must **already bear** `σ = mgu(l, u)`, where `l` is `from`'s
   * side `fromSide` and `u = subtermAt(atomOf(into.iInto), uPos)`: the **caller** (the saturation loop, or
   * the term index in Phase 5) locates the overlap and unifies it — as Vampire's index feeds a substitution
   * to `performSuperposition`. This only applies the post-σ gates and builds
   * `(into[u := r] ∨ into\{iInto} ∨ from\{iFrom}) σ`; it **does not touch the trail** (the caller owns
   * `save` / `unify` / `restore`). `from` uses scope 0, `into` scope 1. `uPos` is the caller's **live**
   * subterm stack ([[IntArrayList]], pushed/popped during the walk); it is copied to a durable array only
   * when the inference fires (for the [[Justification]]).
   *
   * Post-σ gates: `lσ ⋠ rσ` (reject if `rσ ≽ lσ`); if `iInto` is an equality, don't rewrite its
   * strictly-smaller side; the rewritten literal is not a trivial `x ≈ x`. **Preconditions the caller
   * ensures before unifying:** `from`'s literal is a positive equality, `uPos` is non-empty, and `u` is
   * not a variable.
   */
  def superpose(bank: TermBank, trail: Trail, order: Order,
                from: Clause, iFrom: Int, fromSide: Int,
                into: Clause, iInto: Int, uPos: IntArrayList): Option[Clause] =
    val fromAtom: Term = bank.atomOf(from.literals(iFrom))
    val intoLit: Literal = into.literals(iInto)
    val intoAtom: Term = bank.atomOf(intoLit)
    val l: Term = bank.arg(fromAtom, fromSide)
    val r: Term = bank.arg(fromAtom, 1 - fromSide)
    val ap: trail.Applier = trail.applier()
    val lS: Term = ap.apply(l, 0)
    val rS: Term = ap.apply(r, 0)
    if geq(order.kbo.compare(rS, lS)) then None // require lσ ⋠ rσ
    else
      val intoAtomS: Term = ap.apply(intoAtom, 1) // only the into-atom; whole-clause instantiation deferred to build
      // smaller-side gate: don't rewrite the strictly-smaller side of an equality into-literal
      val smallerSideReject: Boolean =
        order.isEqualityAtom(intoAtom) && {
          val aS: Term = bank.arg(intoAtomS, 0); val bS: Term = bank.arg(intoAtomS, 1)
          if uPos.getInt(0) == 0 then order.kbo.compare(aS, bS) == Lt else order.kbo.compare(bS, aS) == Lt
        }
      if smallerSideReject then None
      else
        val pos: Array[Int] = uPos.toIntArray // materialise the position only now that the inference fires
        val newAtom: Term = replaceAt(bank, intoAtomS, pos, rS)
        if bank.isPositive(intoLit) && order.isEqualityAtom(newAtom) && bank.arg(newAtom, 0) == bank.arg(newAtom, 1) then None
        else // committed: instantiate the remaining literals and fill a pre-sized array (size known upfront)
          val intoLitsS: Array[Literal] = into.literals.map(ap.applyLit(_, 1))
          val fromLitsS: Array[Literal] = from.literals.map(ap.applyLit(_, 0))
          val out: Array[Literal] = new Array[Literal](into.literals.length + from.literals.length - 1)
          out(0) = bank.mkLiteral(newAtom, bank.isPositive(intoLit))
          var n = 1
          var k = 0
          while k < into.literals.length do { if k != iInto then { out(n) = intoLitsS(k); n += 1 }; k += 1 }
          k = 0
          while k < from.literals.length do { if k != iFrom then { out(n) = fromLitsS(k); n += 1 }; k += 1 }
          Some(bank.mkClause(out, Justification.Superposition(from, iFrom, fromSide, into, iInto, pos)))

  /**
   * **Equality resolution** — all resolvents of `c` on its **eligible** literals. For each `i` in `eligible`
   * that is a negative equality `s ≠ t` with `σ = mgu(s, t)`, yields `(c\{i})σ`. The callee picks the
   * applicable literals (negative equalities that unify); `eligible` — the `selected`/maximal set — is the
   * loop's contribution.
   */
  def equalityResolution(bank: TermBank, trail: Trail, order: Order, c: Clause, eligible: Array[Int]): List[Clause] =
    eligible.iterator.flatMap(resolveOne(bank, trail, order, c, _)).toList

  private def resolveOne(bank: TermBank, trail: Trail, order: Order, c: Clause, i: Int): Option[Clause] =
    val lit: Literal = c.literals(i)
    val atom: Term = bank.atomOf(lit)
    if bank.isPositive(lit) || !order.isEqualityAtom(atom) then None // only negative equalities
    else
      val s: Term = bank.arg(atom, 0); val t: Term = bank.arg(atom, 1)
      val saved: Int = trail.save()
      val result: Option[Clause] =
        if !trail.unify(s, 0, t, 0) then None
        else
          val ap: trail.Applier = trail.applier()
          val out: Array[Literal] = new Array[Literal](c.literals.length - 1)
          var n = 0
          var k = 0
          while k < c.literals.length do { if k != i then { out(n) = ap.applyLit(c.literals(k), 0); n += 1 }; k += 1 }
          Some(bank.mkClause(out, Justification.EqualityResolution(c, i)))
      trail.restore(saved)
      result

  /**
   * **Equality factoring** — all factors of `c` on its **eligible** positive equalities. For each ordered
   * pair of distinct eligible positive equalities `i` (`s ≈ t`, factored side `iSide` = `s`) and `j`
   * (`s' ≈ t'`, side `jSide` = `s'`) with `σ = mgu(s, s')` and gates `sσ ⋠ tσ` **and** `sσ ⋠ t'σ`, yields
   * `(c\{i} ∨ tσ ≠ t'σ)σ` — **drop the maximal literal `i`, keep the partner `j`**, adding the disequality of
   * their other sides (matching Vampire and E). The callee enumerates the pairs and sides: `iSide` ranges
   * over `i`'s `Gt` side (both if incomparable); `jSide` over both sides of `j` (the gates filter). Which
   * literal is truly maximal — hence which pairs are eligible — is the loop's concern, via `eligible`.
   */
  def equalityFactoring(bank: TermBank, trail: Trail, order: Order, c: Clause, eligible: Array[Int]): List[Clause] =
    val out = List.newBuilder[Clause]
    var a = 0
    while a < eligible.length do
      val i = eligible(a)
      val litI: Literal = c.literals(i)
      val atomI: Term = bank.atomOf(litI)
      if bank.isPositive(litI) && order.isEqualityAtom(atomI) then
        val sides: List[Int] = usableSides(order, atomI)
        var b = 0
        while b < eligible.length do
          val j = eligible(b)
          if j != i then
            val litJ: Literal = c.literals(j)
            val atomJ: Term = bank.atomOf(litJ)
            if bank.isPositive(litJ) && order.isEqualityAtom(atomJ) then
              var ss = sides
              while ss.nonEmpty do
                val iSide = ss.head
                factorOne(bank, trail, order, c, i, atomI, iSide, j, atomJ, 0).foreach(out += _)
                factorOne(bank, trail, order, c, i, atomI, iSide, j, atomJ, 1).foreach(out += _)
                ss = ss.tail
          b += 1
      a += 1
    out.result()

  private def factorOne(bank: TermBank, trail: Trail, order: Order,
                        c: Clause, i: Int, atomI: Term, iSide: Int, j: Int, atomJ: Term, jSide: Int): Option[Clause] =
    val s: Term = bank.arg(atomI, iSide); val t: Term = bank.arg(atomI, 1 - iSide)
    val sp: Term = bank.arg(atomJ, jSide); val tp: Term = bank.arg(atomJ, 1 - jSide)
    val saved: Int = trail.save()
    val result: Option[Clause] =
      if !trail.unify(s, 0, sp, 0) then None
      else
        val ap: trail.Applier = trail.applier()
        val sS: Term = ap.apply(s, 0); val tS: Term = ap.apply(t, 0)
        if geq(order.kbo.compare(tS, sS)) then None // sσ ⋠ tσ
        else
          val tpS: Term = ap.apply(tp, 0) // deferred past the first gate (only reached if it passes)
          if geq(order.kbo.compare(tpS, sS)) then None // sσ ⋠ t'σ
          else
            val out: Array[Literal] = new Array[Literal](c.literals.length) // drop `i`, add tσ ≠ t'σ
            out(0) = bank.mkLiteral(bank.mkApp(EqualitySymbol, Array(tS, tpS)), false) // tσ ≠ t'σ
            var n = 1
            var k = 0
            while k < c.literals.length do { if k != i then { out(n) = ap.applyLit(c.literals(k), 0); n += 1 }; k += 1 }
            Some(bank.mkClause(out, Justification.EqualityFactoring(c, i, iSide, j, jSide)))
    trail.restore(saved)
    result

  /** Factored-side choices for equality atom: its `Gt` side, both if incomparable, none if trivially `Eq`. */
  private def usableSides(order: Order, atom: Term): List[Int] =
    order.orient(atom) match
      case Gt => List(0)
      case Lt => List(1)
      case Inc => List(0, 1)
      case Eq => Nil
