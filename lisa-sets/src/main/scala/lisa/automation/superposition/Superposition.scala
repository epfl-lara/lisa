package lisa.automation.superposition

import scala.collection.mutable
import it.unimi.dsi.fastutil.ints.IntArrayList

import Core.*
import lisa.automation.superposition.ordering.*
import Cmp.*

/** One rewrite a clause offers: read the equality at literal `lit` in the direction that takes its
  * `side` to the other, so `lhs` is the term to be matched against a subterm elsewhere. Which sides qualify is
  * [[Superposition.usesSide]]; [[Superposition.rewriteSources]] collects them and
  * [[Core.Clause.rewriteSources]] memoises that per clause. */
final class RewriteSource(val lit: Int, val side: Int, val lhs: Term):
  override def toString: String = s"RewriteSource(lit=$lit, side=$side)"

/** Superposition, equality resolution and equality factoring. The latter two follow [[Inference]]'s shape:
  * save the trail, unify, check the ordering conditions, build the conclusion, restore. [[superpose]] splits
  * it, because the caller locates the overlap and has already unified when it calls in, so it only checks and
  * builds and the caller owns the surrounding save, unify and restore.
  *
  * Eligibility is the loop's concern, not these functions'. These functions check only the term-orientation conditions, independent of selection.
  *
  * A subterm position is a path of argument indices into an atom, of length at least one, since superposition
  * rewrites neither into a variable nor at the atom root. */
object Superposition:

  // --- position helpers -----------------------------------------------------------------------------------
  //
  // A subterm position is a path of argument indices into an atom (root excluded), represented as
  // `Array[Int]`. It is only *materialised* when an inference fires and must record it in a `Justification`.

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

  /** Visit every **non-variable** proper subterm of `atom` (root excluded), leftmost-outermost, calling
    * `visit(u, path)` with the subterm `u` and its current position. The `path` [[IntArrayList]] is a single
    * stack reused across the whole traversal (pushed on descent, popped on return), so enumeration
    * allocates nothing per position. Snapshot it (`path.toIntArray`) inside `visit` **only** when you keep
    * the position, i.e. when an inference actually fires. `visit` returns `true` to stop the traversal
    * early. */
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

  // --- inference rules ------------------------------------------------------------------------------------

  /** Whether `c` is `Gt` or `Eq` (i.e. `a ≽ b` when `c = compare(a, b)`). */
  private inline def geq(c: Cmp): Boolean = c == Gt || c == Eq

  /** Superposition, checking and building only. The trail must already carry the unifier of `l`, which is
    * `from`'s side `fromSide`, with the subterm of `into` at `uPos`; the caller locates the overlap, unifies
    * it, and owns the surrounding save and restore. `from` is in scope 0 and `into` in scope 1.
    *
    * Checks after the substitution that `l` has not become smaller than `r`, that a smaller side of an
    * equality is not being rewritten, and that the result is not a trivial `x ≈ x`. The caller must have
    * ensured before unifying that `from`'s literal is a positive equality and that `u` is a non-variable
    * proper subterm. `uPos` is the caller's live position stack, copied only when the inference fires. */
  def superpose(bank: TermBank, trail: Trail,
                from: Clause, iFrom: Int, fromSide: Int,
                into: Clause, iInto: Int, uPos: IntArrayList): Option[Clause] =
    val order: Order = bank.order
    val fromAtom: Term = bank.atomOf(from.literals(iFrom))
    val intoLit: Literal = into.literals(iInto)
    val intoAtom: Term = bank.atomOf(intoLit)
    val l: Term = bank.arg(fromAtom, fromSide)
    val r: Term = bank.arg(fromAtom, 1 - fromSide)
    val ap: trail.Applier = trail.applier()
    val lS: Term = ap.apply(l, 0) // applied even where unused below: `replayApplier` reproduces these calls
    val rS: Term = ap.apply(r, 0)
    // `lσ ⋠ rσ` can only fail if σ flips the two sides, so it needs comparing only for an equation used in a
    // direction the ordering does not already fix: KBO is stable under substitution, so `l ≻ r` gives `lσ ≻ rσ`.
    // `rewriteSources` offers the greater direction of every orientable equation, so this skips the comparison
    // on most overlaps; a caller taking another direction (the tests do) is still checked.
    val ori: Cmp = order.orient(fromAtom) // memoised, and already computed for this atom by `rewriteSources`
    val usedGreaterSide: Boolean = (ori == Gt && fromSide == 0) || (ori == Lt && fromSide == 1)
    if !usedGreaterSide && geq(order.kbo.compare(rS, lS)) then None
    else
      val intoAtomS: Term = ap.apply(intoAtom, 1) // only the into-atom; whole-clause instantiation deferred to build
      // smaller-side gate: don't rewrite the strictly-smaller side of an equality into-literal
      val smallerSideReject: Boolean =
        bank.isEqualityAtom(intoAtom) && {
          val aS: Term = bank.arg(intoAtomS, 0); val bS: Term = bank.arg(intoAtomS, 1)
          if uPos.getInt(0) == 0 then order.kbo.compare(aS, bS) == Lt else order.kbo.compare(bS, aS) == Lt
        }
      if smallerSideReject then None
      else
        val pos: Array[Int] = uPos.toIntArray
        val newAtom: Term = replaceAt(bank, intoAtomS, pos, rS)
        if bank.isPositive(intoLit) && bank.isEqualityAtom(newAtom) && bank.arg(newAtom, 0) == bank.arg(newAtom, 1) then None
        else // committed: instantiate the kept literals straight into a pre-sized array (size known upfront).
          // The dropped literals (`iInto`, `iFrom`) are skipped: `iInto`'s variables were all registered via
          // `intoAtomS` and `iFrom`'s (its atom is exactly `l = r`) via `lS`/`rS` above, so the output variable
          // numbering is identical to applying them, so this just avoids two throwaway arrays and instantiating
          // the two literals we discard.
          val out: Array[Literal] = new Array[Literal](into.literals.length + from.literals.length - 1)
          out(0) = bank.mkLiteral(newAtom, bank.isPositive(intoLit))
          val n1 = ap.copyLitsExcept(into.literals, iInto, 1, out, 1)
          ap.copyLitsExcept(from.literals, iFrom, 0, out, n1)
          Some(bank.mkClause(out, Justification.Superposition(from, iFrom, fromSide, into, iInto, pos)))

  /** Reproduces [[superpose]]'s `Applier` order, so that reconstruction numbers the conclusion's fresh variables as it did.
    */
  private[superposition] def replayApplier(bank: TermBank, ap: Trail#Applier,
                                           from: Clause, iFrom: Int, fromSide: Int,
                                           into: Clause, iInto: Int): Unit =
    val fromAtom: Term = bank.atomOf(from.literals(iFrom))
    ap.apply(bank.arg(fromAtom, fromSide), 0) //     l, as in `superpose`
    ap.apply(bank.arg(fromAtom, 1 - fromSide), 0) // r
    ap.apply(bank.atomOf(into.literals(iInto)), 1) // the into-atom
    var k = 0 //                                      then the survivors, skipping the two dropped literals
    while k < into.literals.length do { if k != iInto then ap.apply(bank.atomOf(into.literals(k)), 1); k += 1 }
    k = 0
    while k < from.literals.length do { if k != iFrom then ap.apply(bank.atomOf(from.literals(k)), 0); k += 1 }

  /** **Equality resolution**: all resolvents of `c` on its **eligible** literals. For each `i` in `eligible`
    * that is a negative equality `s ≠ t` with `σ = mgu(s, t)`, yields `(c\{i})σ`. The callee picks the
    * applicable literals (negative equalities that unify), and `eligible`, the `selected`/maximal set, is the
    * loop's contribution. */
  def equalityResolution(bank: TermBank, trail: Trail, c: Clause, eligible: Array[Int]): List[Clause] =
    val out = List.newBuilder[Clause]
    var a = 0
    while a < eligible.length do
      resolveOne(bank, trail, c, eligible(a)).foreach(out += _)
      a += 1
    out.result()

  /** No ordering condition here beyond eligibility, which the caller supplies, hence no [[Order]] parameter. */
  private def resolveOne(bank: TermBank, trail: Trail, c: Clause, i: Int): Option[Clause] =
    val lit: Literal = c.literals(i)
    val atom: Term = bank.atomOf(lit)
    if bank.isPositive(lit) || !bank.isEqualityAtom(atom) then None // only negative equalities
    else
      val s: Term = bank.arg(atom, 0); val t: Term = bank.arg(atom, 1)
      val saved: Int = trail.save()
      val result: Option[Clause] =
        if !trail.unify(s, 0, t, 0) then None
        else
          val ap: trail.Applier = trail.applier()
          val out: Array[Literal] = new Array[Literal](c.literals.length - 1)
          ap.copyLitsExcept(c.literals, i, 0, out, 0)
          Some(bank.mkClause(out, Justification.EqualityResolution(c, i)))
      trail.restore(saved)
      result

  /** Equality factoring. From a factored literal `i` and a partner `j` whose chosen sides unify, derives `c`
    * without `i`, with the disequality of the two other sides added. Both side choices are enumerated here and
    * filtered by the ordering conditions.
    *
    * Only `i` must be eligible; the partner is any other positive equality of `c`. Drawing the partner from
    * `eligible` as well would lose inferences: in `f(x) ≈ a ∨ f(x) ≈ d` with `d ≻ a` only the second literal
    * is eligible, so the legitimate factor `d ≉ a ∨ f(x) ≈ a` would never be derived. */
  def equalityFactoring(bank: TermBank, trail: Trail, c: Clause, eligible: Array[Int]): List[Clause] =
    val order: Order = bank.order
    val out = List.newBuilder[Clause]
    var a = 0
    while a < eligible.length do
      val i = eligible(a)
      val litI: Literal = c.literals(i)
      val atomI: Term = bank.atomOf(litI)
      if bank.isPositive(litI) && bank.isEqualityAtom(atomI) then
        val oriI: Cmp = order.orient(atomI) // once per eligible literal; `usesSide` reads it per side
        var j = 0
        while j < c.literals.length do
          if j != i then
            val litJ: Literal = c.literals(j)
            val atomJ: Term = bank.atomOf(litJ)
            if bank.isPositive(litJ) && bank.isEqualityAtom(atomJ) then
              var iSide = 0
              while iSide < 2 do
                if usesSide(oriI, iSide) then
                  factorOne(bank, trail, order, c, i, atomI, iSide, j, atomJ, 0).foreach(out += _)
                  factorOne(bank, trail, order, c, i, atomI, iSide, j, atomJ, 1).foreach(out += _)
                iSide += 1
          j += 1
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
            ap.copyLitsExcept(c.literals, i, 0, out, 1)
            Some(bank.mkClause(out, Justification.EqualityFactoring(c, i, iSide, j, jSide)))
    trail.restore(saved)
    result

  /** Reproduces [[factorOne]]'s `Applier` order (`s`, `t`, `t'`, then the survivors, skipping `i`); see
   *  [[replayApplier]]. Change one and change the other. */
  private[superposition] def replayFactoringApplier(bank: TermBank, ap: Trail#Applier,
                                                    c: Clause, i: Int, iSide: Int, j: Int, jSide: Int): Unit =
    val atomI: Term = bank.atomOf(c.literals(i))
    ap.apply(bank.arg(atomI, iSide), 0) //                            s
    ap.apply(bank.arg(atomI, 1 - iSide), 0) //                        t
    ap.apply(bank.arg(bank.atomOf(c.literals(j)), 1 - jSide), 0) //   t'
    var k = 0
    while k < c.literals.length do { if k != i then ap.apply(bank.atomOf(c.literals(k)), 0); k += 1 }

  /** Whether an equality atom oriented `ori` may be used as a rewrite in the direction that takes its `side` to
    * the other: only the greater side, or either side when the two are incomparable, and neither when they are
    * equal. */
  private inline def usesSide(ori: Cmp, side: Int): Boolean = ori match
    case Gt  => side == 0
    case Lt  => side == 1
    case Inc => true
    case Eq  => false

  /** The rewrites `c` offers superposition: for each of its **selected** positive equalities, each side that
    * [[usesSide]] admits and that is not itself a variable.
    *
    * The selection is read from the clause rather than passed in, so that the index and the loop cannot disagree
    * about which literals are eligible; the index would otherwise leak entries. Call
    * [[Core.Clause.rewriteSources]], which memoises this, rather than this directly. */
  def rewriteSources(bank: TermBank, c: Clause): Array[RewriteSource] =
    val order: Order = bank.order
    val sel: Array[Int] = c.select(bank)
    val out = mutable.ArrayBuffer.empty[RewriteSource]
    var i = 0
    while i < sel.length do
      val iLit: Int = sel(i)
      val lit: Literal = c.literals(iLit)
      val atom: Term = bank.atomOf(lit)
      if bank.isPositive(lit) && bank.isEqualityAtom(atom) then
        val ori: Cmp = order.orient(atom)
        var side = 0
        while side < 2 do
          if usesSide(ori, side) then
            val lhs: Term = bank.arg(atom, side)
            if !bank.isVar(lhs) then out += new RewriteSource(iLit, side, lhs)
          side += 1
      i += 1
    out.toArray
