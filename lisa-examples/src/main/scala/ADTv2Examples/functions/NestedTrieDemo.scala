package ADTv2Examples.functions

import lisa.maths.SetTheory.Types.ADTv2.*
import lisa.maths.SetTheory.Types.ADTv2.API.`*`
import lisa.maths.SetTheory.Types.ADTv2.library.Bool.*
import lisa.maths.SetTheory.Types.ADTv2.library.List.*
import lisa.maths.SetTheory.Types.ADTv2.library.Nat.*
import lisa.maths.SetTheory.Types.ADTv2.library.Option.*
import lisa.maths.SetTheory.Types.ADTv2.library.*
import lisa.maths.SetTheory.Types.ADTv2.interface.{ADT, Constructor}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.NestedTrie
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.NestedTrieProofs
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.NestedTrieProofs.RPat
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.NestedConstructorPattern
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.existsSeq

/**
 * Runs the real-typed nested-pattern scope checker (NestedTrie) against the live
 * nat / Option / List ADT definitions. No proofs — prints the decision trie and
 * the IN SCOPE / REJECTED verdict for each example.
 */
object NestedTrieDemo extends lisa.Main {

  private val k = variable[Ind]
  private val t = variable[Ind]

  // Each clause is its top constructor + the value-argument terms.
  type Clauses = Seq[(Constructor[?], Seq[Expr[Ind]])]

  // Guard terms are built with the `*` set-application operator, exactly as the
  // `Case(...)` DSL does (e.g. `succ * k` is `app(succ)(k)`); nullary guards are
  // the bare constructor symbols (`zero`, `nil`).
  private val z: Expr[Ind]        = zero
  private def s(p: Expr[Ind])     = succ * p

  private val examples: Seq[(String, ADT[?], Seq[Expr[Ind]], Clauses)] = Seq(
    ("isOptionZero", option, Seq(nat), Seq(
      (none, Seq.empty),
      (some, Seq(z)),
      (some, Seq(s(k))))),

    ("isGreaterThanOne", nat, Seq.empty, Seq(
      (zero, Seq.empty),
      (succ, Seq(z)),
      (succ, Seq(s(k))))),

    ("isGreaterThanTwo", nat, Seq.empty, Seq(
      (zero, Seq.empty),
      (succ, Seq(z)),
      (succ, Seq(s(z))),
      (succ, Seq(s(s(k)))))),

    // non-exhaustive: zero branch dropped
    ("missingZero", nat, Seq.empty, Seq(
      (succ, Seq(z)),
      (succ, Seq(s(k))))),

    // overlap: catch-all succ(k) collides with succ(zero)
    ("overlapping", nat, Seq.empty, Seq(
      (zero, Seq.empty),
      (succ, Seq(z)),
      (succ, Seq(k)))),

    // depth-2: split a list of nats on whether its head is zero (tail is a binder)
    ("listHeadZero", list, Seq(nat), Seq(
      (nil, Seq.empty),
      (cons, Seq(z, t)),
      (cons, Seq(s(k), t)))),
  )

  examples.foreach { (name, adt, typeArgs, clauses) =>
    println(NestedTrie.analyze(name, adt, typeArgs, clauses))
  }

  // ── Step 2: kernel-checked disjointness proofs ─────────────────────────────
  private def cl(c: Constructor[?], args: Expr[Ind]*): RPat =
    RPat.RCon(c, args.map(NestedTrieProofs.parse).toList)

  private val natTy = (nat, Seq.empty[Expr[Ind]])
  private val optTy = (option, Seq[Expr[Ind]](nat))

  // (domain, label, p, q) for several disjoint pairs at varying divergence depth.
  private val disjointPairs = Seq(
    (natTy, "zero ⊥ succ(zero)               [root]",       cl(zero),        cl(succ, z)),
    (natTy, "succ(zero) ⊥ succ(succ k)    [depth 1]",    cl(succ, z),     cl(succ, s(k))),
    (natTy, "succ(succ 0) ⊥ succ(succ(succ k)) [d2]", cl(succ, s(z)),  cl(succ, s(s(k)))),
    (optTy, "some(zero) ⊥ some(succ k)       [poly]",    cl(some, z),     cl(some, s(k))),
  )

  println("══════════ disjointness proofs (kernel-checked) ══════════")
  disjointPairs.foreach { (dom, label, p, q) =>
    val thm = NestedTrieProofs.incompatibleProof(dom, p, q)
    println(s"  ✓ $label\n      ⊢ ${thm.statement}")
  }

  // ── Step 2: kernel-checked coverage proofs ─────────────────────────────────
  private type Clause = (Constructor[?], Seq[Expr[Ind]])
  private val coverageCases: Seq[(String, (ADT[?], Seq[Expr[Ind]]), Seq[Clause])] = Seq(
    ("isGreaterThanOne", natTy, Seq((zero, Seq.empty), (succ, Seq(z)), (succ, Seq(s(k))))),
    ("isGreaterThanTwo", natTy, Seq((zero, Seq.empty), (succ, Seq(z)), (succ, Seq(s(z))), (succ, Seq(s(s(k)))))),
    ("isOptionZero",     optTy, Seq((none, Seq.empty), (some, Seq(z)), (some, Seq(s(k))))),
    ("listHeadZero",     (list, Seq[Expr[Ind]](nat)), Seq((nil, Seq.empty), (cons, Seq(z, t)), (cons, Seq(s(k), t)))),
  )

  println("══════════ coverage proofs (kernel-checked) ══════════")
  coverageCases.foreach { (label, dom, cls) =>
    val thm = NestedTrieProofs.coverageProof(dom, cls)
    println(s"  ✓ $label\n      ⊢ ${thm.statement}")
  }

  // ── Step 1: binder-model check (build patterns via fromArgs, no validation) ──
  private val term = variable[Ind]
  private def disjunctOf(p: lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern[?]) =
    existsSeq(p.variables2, p.freshBranchPremise /\ (term === p.freshInputTerm))

  println("══════════ Step 1: inner-binder tracking ══════════")

  // Nullary guard `cons(tru, tl)` — must be a NO-OP (no inner binders).
  private val consTrue = NestedConstructorPattern.fromArgs(
    cons.semantic, Seq(Right(tru), Left(t)), t, Seq.empty, list.termAt(Seq(bool)))
  println(s"  cons(tru, tl):  binders = ${consTrue.binders.mkString(", ")}   (inner: ${consTrue.innerBinders.mkString(",")})")

  // Non-nullary guard `succ(succ k)` over nat — `k` must now be bound.
  private val succNested = NestedConstructorPattern.fromArgs(
    succ.semantic, Seq(Right(s(s(k)))), k, Seq.empty, nat.termAt(Seq.empty))
  println(s"  succ(succ(k)):  binders = ${succNested.binders.mkString(", ")}   (inner: ${succNested.innerBinders.mkString(",")})")
  println(s"      caseCoverage disjunct = ${disjunctOf(succNested)}")

  // ── coverage in caseCoverage shape for isGreaterThanTwo's patterns ──────────
  private def mkPat(c: Constructor[?], gs: Expr[Ind]*) =
    NestedConstructorPattern.fromArgs(
      c.semantic, gs.map(g => Right(g): Either[Variable[Ind], Expr[Ind]]), zero,
      Seq.empty, nat.termAt(Seq.empty))

  private val gt2Clauses: Seq[(Constructor[?], Seq[Expr[Ind]])] = Seq(
    (zero, Seq.empty), (succ, Seq(z)), (succ, Seq(s(z))), (succ, Seq(s(s(k)))))
  private val gt2Patterns = gt2Clauses.map((c, gs) => mkPat(c, gs*))

  println("══════════ coverage (caseCoverage shape) — isGreaterThanTwo ══════════")
  private val gt2Coverage = NestedTrieProofs.coverageCaseShape(natTy, gt2Clauses, gt2Patterns)
  println(s"  ✓ ⊢ ${gt2Coverage.statement}")

  println("══════════ incompatible (trait shape) — isGreaterThanTwo pairs ══════════")
  private val gt2Pairs = Seq(
    ("zero ⊥ succ(zero)        [cross]",  0, 1),
    ("succ(0) ⊥ succ(succ 0)   [same,d1]", 1, 2),
    ("succ(succ 0) ⊥ succ(succ(succ k)) [same,d2]", 2, 3))
  gt2Pairs.foreach { (label, i, j) =>
    val thm = NestedTrieProofs.incompatibleCaseShape(gt2Patterns(i), gt2Patterns(j))
    println(s"  ✓ $label\n      ⊢ ${thm.statement}")
  }

  // ── branchSelectionFor (multi-level) standalone — halve's `succ` patterns ────
  println("══════════ branchSelectionFor (multi-level) — succ{zero, succ k} ══════════")
  private val aTerm = variable[Ind]
  private val k3 = variable[Ind]
  private val halveSuccPats = Seq(mkPat(succ, z), mkPat(succ, s(k3)))
  private val bsf = NestedTrieProofs.branchSelectionForCaseShape(succ.semantic, succ, aTerm, halveSuccPats, Seq.empty)
  println(s"  ✓ ⊢ ${bsf.statement}")

  // ── recFun + multi-level nested patterns — end-to-end verification ───────────
  println("══════════ recFun + multi-level patterns ══════════")
  private val kk = variable[Ind]
  // halve : 0,1 ↦ 0 ;  n+2 ↦ halve(n)+1   (multi-level guard `succ(succ k)` + recursion)
  val halve = recFun(nat, nat) { self =>
    Case(zero):
      zero
    Case(succ, zero):
      zero
    Case(succ, succ * kk):
      succ * (self * kk)
  }
  show(halve.intro)
  show(halve.elimTotal)
  println("  ✓ recFun with multi-level patterns WORKS")
}
