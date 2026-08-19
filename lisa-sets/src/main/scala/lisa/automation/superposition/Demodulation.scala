package lisa.automation.superposition

import it.unimi.dsi.fastutil.ints.IntArrayList

import Core.*
import lisa.automation.superposition.ordering.*
import lisa.automation.superposition.index.*

/** Rewriting by positive unit equalities. Forward demodulation normal-forms a clause against the active
  * equations, backward demodulation rewrites active clauses with a new one. Each step replaces a subterm by a
  * strictly smaller instance, so repeated steps terminate, and each records its own justification. */
object Demodulation:

  /** A usable rewrite direction extracted from a positive unit equality clause: `lhs → rhs`. `lhsVars` are
   *  the distinct variables of `lhs`, precomputed once (they're invariant) for the renaming redundancy check.
   *
   *  Identity is `(source.id, side)`, which determines the rest, so that a rule re-derived from its clause
   *  deletes the stored one. */
  final class Rule(val source: Clause, val side: Int, val lhs: Term, val rhs: Term, val oriented: Boolean, val lhsVars: Array[Term]):
    override def equals(o: Any): Boolean = o match
      case r: Rule => source.id == r.source.id && side == r.side
      case _       => false
    override def hashCode: Int = source.id * 31 + side
    override def toString: String = s"Rule(c${source.id}, side=$side)"

  /** Whether `c` is a positive unit equality. */
  def isPositiveUnitEquality(bank: TermBank, c: Clause): Boolean =
    c.literals.length == 1 && bank.isPositive(c.literals(0)) &&
      bank.isEquality(c.literals(0))

  /** The usable rewrite directions of `eq` as a demodulator: `Nil` unless `eq` is a positive unit equality.
    * Oriented equations rewrite from the `Gt` side; unoriented ones rewrite from a side only if that side's
    * variables cover the other's (so no fresh variable is introduced) and it is not itself a variable. */
  def rules(bank: TermBank, eq: Clause): List[Rule] =
    if eq.literals.length != 1 then Nil
    else
      val order: Order = bank.order
      val lit = eq.literals(0)
      val atom = bank.atomOf(lit)
      if !bank.isPositive(lit) || !bank.isEqualityAtom(atom) then Nil
      else
        val s0 = bank.arg(atom, 0); val s1 = bank.arg(atom, 1)
        def mk(side: Int, lhs: Term, rhs: Term, oriented: Boolean, lhsVars: Array[Term]): Rule =
          new Rule(eq, side, lhs, rhs, oriented, lhsVars)
        order.orient(atom) match
          case Cmp.Gt => if bank.isVar(s0) then Nil else List(mk(0, s0, s1, true, bank.varsOf(s0)))
          case Cmp.Lt => if bank.isVar(s1) then Nil else List(mk(1, s1, s0, true, bank.varsOf(s1)))
          case Cmp.Eq => Nil
          case Cmp.Inc =>
            var rs: List[Rule] = Nil
            // side 0 as LHS needs vars(s1) ⊆ vars(s0); side 1 as LHS needs vars(s0) ⊆ vars(s1)
            if !bank.isVar(s1) && bank.varsSubsetOf(s0, s1) then rs = mk(1, s1, s0, false, bank.varsOf(s1)) :: rs
            if !bank.isVar(s0) && bank.varsSubsetOf(s1, s0) then rs = mk(0, s0, s1, false, bank.varsOf(s0)) :: rs
            rs

  /** Rewrite `clause` to a normal form by repeating `step` until it stops firing. Each step replaces a subterm
   *  by a strictly smaller instance, so this terminates. One closure per call, not per step. */
  private def fixpoint(clause: Clause)(step: Clause => Option[Clause]): Clause =
    var cur: Clause = clause
    var next: Option[Clause] = step(cur)
    while next.isDefined do
      cur = next.get
      next = step(cur)
    cur

  /** Forward demodulation against an explicit rule set: the shape backward demodulation needs, where the rules
   *  are the ones extracted from the single new unit equality. */
  def normalForm(bank: TermBank, trail: Trail, clause: Clause, rules: Array[Rule]): Clause =
    if rules.isEmpty then clause
    else
      val order: Order = bank.order
      fixpoint(clause)(rewriteOnce(bank, trail, order, _, rules))

  /** Forward demodulation against a [[DiscriminationTree]] of demodulators, which is how the loop rewrites the
   *  given clause against the whole active rule set: each subterm's matching demodulators come from one tree
   *  descent (with σ built on the trail) rather than a scan of every rule. */
  def normalFormIndexed(bank: TermBank, trail: Trail, clause: Clause, tree: DiscriminationTree[Rule]): Clause =
    if tree.isEmpty then clause
    else
      val order: Order = bank.order
      fixpoint(clause)(rewriteOnceIndexed(bank, trail, order, _, tree))

  // --- one rewrite step -----------------------------------------------------------------------------------

  /** Walk the subterm positions of every literal,  calling `attempt(iLit, u, path)` on the
   *  subterm `u` at `path` of literal `iLit` and stopping as soon as it returns `true`. Positions come from a
   *  reused stack ([[Superposition.foreachSubterm]]) and one is materialised only when a rewrite fires (in
   *  [[applyRuleAt]]). */
  private inline def firstRewrite(bank: TermBank, c: Clause)(inline attempt: (Int, Term, IntArrayList) => Boolean): Unit =
    var iLit = 0
    var stopped = false
    while iLit < c.literals.length && !stopped do
      val li: Int = iLit // the subterm-walk closure cannot capture the loop `var`
      stopped = Superposition.foreachSubterm(bank, bank.atomOf(c.literals(li))) { (u, path) => attempt(li, u, path) }
      iLit += 1

  /** The first applicable single rewrite of `c` by any rule of `rules`, which are scanned per subterm. */
  private def rewriteOnce(bank: TermBank, trail: Trail, order: Order, c: Clause, rules: Array[Rule]): Option[Clause] =
    var found: Option[Clause] = None
    firstRewrite(bank, c) { (li, u, path) =>
      var ri = 0
      while ri < rules.length && found.isEmpty do
        found = tryRewrite(bank, trail, order, c, li, path, u, rules(ri))
        ri += 1
      found.isDefined
    }
    found

  /** The first applicable single rewrite of `c` via the discrimination-tree index: each subterm's matching rules
   *  come from one tree descent (`retrieveGeneralizations`, which leaves σ on the trail) rather than a scan, so
   *  [[applyRuleAt]] runs the gates and the build with σ already in place. */
  private def rewriteOnceIndexed(bank: TermBank, trail: Trail, order: Order, c: Clause, tree: DiscriminationTree[Rule]): Option[Clause] =
    var found: Option[Clause] = None
    firstRewrite(bank, c) { (li, u, path) =>
      tree.retrieveGeneralizations(u) { rule => // σ (rule.lhs onto u) is live on the trail inside this callback
        found = applyRuleAt(bank, trail, order, c, li, path, rule)
        found.isDefined // stop the tree descent once a rewrite fires
      }
      found.isDefined // stop the subterm walk once a rewrite fires
    }
    found

  private def tryRewrite(bank: TermBank, trail: Trail, order: Order,
                         c: Clause, iLit: Int, path: IntArrayList, u: Term, rule: Rule): Option[Clause] =
    val saved = trail.save()
    val result: Option[Clause] =
      if !trail.matchTerm(rule.lhs, 0, u, 1) then None // match rule LHS (scope 0) onto the subterm (scope 1)
      else applyRuleAt(bank, trail, order, c, iLit, path, rule)
    trail.restore(saved)
    result

  /** Post-match rewrite: with the matcher σ (`rule.lhs` onto the subterm at `path`) **already on the trail**,
   *  apply the orientation and redundancy gates and build the rewritten clause, or `None` if a gate rejects.
   *  Shared by the scan ([[tryRewrite]]) and the indexed ([[rewriteOnceIndexed]]) paths, the latter getting σ from
   *  the discrimination-tree descent instead of a separate `matchTerm`. Does not touch the trail. */
  private def applyRuleAt(bank: TermBank, trail: Trail, order: Order,
                          c: Clause, iLit: Int, path: IntArrayList, rule: Rule): Option[Clause] =
    val ap: trail.Applier = trail.applier()
    val lS: Term = ap.apply(rule.lhs, 0)
    val rS: Term = ap.apply(rule.rhs, 0)
    // orientation re-check on the instance (skip for an already-oriented rule)
    if !rule.oriented && order.kbo.compare(lS, rS) != Cmp.Gt then None
    else
      val lit: Literal = c.literals(iLit) // the rewritten literal + its atom, read once for the gate and the build
      val atom: Term = bank.atomOf(lit)
      /** Whether rewriting `lit` at `path` (yielding the instance `rS` on that side) keeps the premise
        * redundant, i.e. whether the rewrite may simplify (delete/replace) `c`.*/
      val premiseRedundant: Boolean =
        val wholeSide = bank.isEqualityAtom(atom) && path.size() == 1
        if !wholeSide then true // rewriting inside a subterm / a non-equality literal: always redundant
        else if !bank.isPositive(lit) || c.literals.length != 1 then true // check only bites on positive unit equalities
        else
          val side: Int = path.getInt(0)
          val otherS = ap.apply(bank.arg(atom, 1 - side), 1) // the untouched side, instantiated
          // rewrote the larger side downward ⇒ redundant; else redundant iff the matcher is a proper instance
          order.kbo.compare(rS, otherS) == Cmp.Lt || !matcherIsRenaming(bank, ap, rule.lhsVars)
      if !premiseRedundant then None
      else
        val pos: Array[Int] = path.toIntArray // materialise the position only now that the rewrite fires
        val newLits = new Array[Literal](c.literals.length)
        var k = 0
        while k < c.literals.length do
          newLits(k) =
            if k == iLit then // the rewritten literal: instantiate its atom, then replace u by r at `pos`
              bank.mkLiteral(Superposition.replaceAt(bank, ap.apply(atom, 1), pos, rS), bank.isPositive(lit))
            else ap.applyLit(c.literals(k), 1)
          k += 1
        Some(bank.mkClause(newLits, Justification.Demodulation(c, iLit, pos, rule.source, rule.side)))

  /** Reproduces [[applyRuleAt]]'s `Applier` order (the rule's two sides, then the target's literals in index
   *  order); see [[Superposition.replayApplier]]. Change one and change the other. */
  private[superposition] def replayApplier(bank: TermBank, ap: Trail#Applier,
                                           rule: Clause, ruleSide: Int, target: Clause): Unit =
    val ruleAtom: Term = bank.atomOf(rule.literals(0)) // the demodulator is a positive unit equality
    ap.apply(bank.arg(ruleAtom, ruleSide), 0) //     the rule's lhs
    ap.apply(bank.arg(ruleAtom, 1 - ruleSide), 0) // its rhs
    var k = 0
    while k < target.literals.length do { ap.apply(bank.atomOf(target.literals(k)), 1); k += 1 }

  /** Whether the matcher σ, restricted to the rule's LHS variables (precomputed on the [[Rule]]), is a variable
   *  renaming (injective onto variables). Explicit loops rather than `lhsVars.map(ap.apply(_, 0)).distinct`:
   *  that would allocate a mapped array and a boxing `distinct`, and compute every image before testing any. */
  private def matcherIsRenaming(bank: TermBank, ap: Trail#Applier, lhsVars: Array[Term]): Boolean =
    val n = lhsVars.length
    if n == 0 then true
    else if n == 1 then bank.isVar(ap.apply(lhsVars(0), 0)) // the common case: no array at all
    else
      val images = new Array[Term](n)
      var i = 0
      while i < n do
        val image: Term = ap.apply(lhsVars(i), 0)
        if !bank.isVar(image) then return false
        var j = 0
        while j < i do
          if images(j) == image then return false // two LHS variables share an image: not injective
          j += 1
        images(i) = image
        i += 1
      true
