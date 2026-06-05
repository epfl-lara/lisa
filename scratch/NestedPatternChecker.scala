//> using scala 3.8.2
//
// Prototype: scope checker for multi-level nested patterns WITHOUT priority.
//
// Pure Scala, no proofs. Decides whether a `Case` set would be accepted by the
// proposed multi-level nested-pattern system, i.e. whether it is
//   (1) well-formed   (every constructor used exists with the right arity at its
//                       position),
//   (2) pairwise DISJOINT (the "no priority / no overlap" guarantee), and
//   (3) EXHAUSTIVE     (covers the whole domain), with a counter-example witness
//                       when it is not.
//
// This mirrors the semantic layer: a `Case(c, a1, ..., an)` already arrives as a
// head constructor plus a list of argument *terms*, where each argument is either
// a variable binder (Left) or a nested constructor application (Right). Here we
// model that directly as the `Pat` tree.

object NestedPatternChecker:

  // ── Faithful (but lightweight) ADT model ──────────────────────────────────
  // A constructor's signature is the list of ADT names of its arguments.
  // arity == argTypes.length. This is exactly what `semanticSignature2` carries.
  final case class Ctor(name: String, argTypes: List[String]):
    def arity: Int = argTypes.length
  final case class Adt(name: String, ctors: List[Ctor])

  final class Registry(adts: Map[String, Adt]):
    def adt(name: String): Adt =
      adts.getOrElse(name, sys.error(s"unknown ADT '$name'"))
    def ctor(adtName: String, ctorName: String): Option[Ctor] =
      adt(adtName).ctors.find(_.name == ctorName)

  // ── Pattern AST (the proposed `Pat`) ──────────────────────────────────────
  enum Pat:
    case PVar(name: String)                 // fresh binder, matches anything
    case PCon(ctor: String, args: List[Pat])
  import Pat.*

  def wild: Pat = PVar("_")
  def wilds(n: Int): List[Pat] = List.fill(n)(wild)

  def show(p: Pat): String = p match
    case PVar(n)         => n
    case PCon(c, Nil)    => c
    case PCon(c, args)   => s"$c(${args.map(show).mkString(", ")})"
  def showRow(r: List[Pat]): String = r.map(show).mkString(", ")

  // ── (1) Well-formedness / type-checking ───────────────────────────────────
  // Every PCon must be a constructor of the ADT expected at its position, with
  // the correct arity; recurse into argument positions using the constructor's
  // signature.
  def typeErrors(reg: Registry, p: Pat, adtName: String): List[String] = p match
    case PVar(_) => Nil
    case PCon(c, args) =>
      reg.ctor(adtName, c) match
        case None =>
          List(s"'$c' is not a constructor of $adtName")
        case Some(ct) if ct.arity != args.length =>
          List(s"$c expects ${ct.arity} arg(s) but got ${args.length}")
        case Some(ct) =>
          args.zip(ct.argTypes).flatMap((a, t) => typeErrors(reg, a, t))

  // ── (2) Pairwise disjointness (no priority) ───────────────────────────────
  // Two patterns are *compatible* (can match a common value) iff at every
  // position where both fix a constructor, the constructors agree. A wildcard is
  // compatible with anything. Overlap == compatibility; the no-priority system
  // requires every pair to be disjoint (incompatible).
  def compatible(p: Pat, q: Pat): Boolean = (p, q) match
    case (PVar(_), _) | (_, PVar(_)) => true
    case (PCon(c, ps), PCon(d, qs)) =>
      c == d && ps.lazyZip(qs).forall(compatible)

  // A concrete witness value (no PVar) in the intersection of two compatible
  // patterns — useful to show *why* they overlap.
  def meet(p: Pat, q: Pat): Pat = (p, q) match
    case (PVar(_), o)              => ground(o)
    case (o, PVar(_))              => ground(o)
    case (PCon(c, ps), PCon(_, qs)) => PCon(c, ps.lazyZip(qs).map(meet).toList)
  // Replace remaining wildcards with a canonical constructor so the witness is a
  // concrete value. (Picks the first constructor; recursion terminates because we
  // only descend through already-finite patterns / chosen constructors once.)
  def ground(p: Pat): Pat = p match
    case PCon(c, args) => PCon(c, args.map(ground))
    case PVar(_)       => PVar("?")   // position unconstrained; left abstract

  // ── (3) Exhaustiveness, via Maranget's matrix algorithm ───────────────────
  // Specialize a matrix by constructor c: keep rows whose first column is c or a
  // wildcard; expand the first column into c's argument columns.
  type Row = List[Pat]
  def specialize(rows: List[Row], c: Ctor): List[Row] =
    rows.flatMap { row =>
      row.head match
        case PCon(c.name, args) => Some(args ++ row.tail)
        case PCon(_, _)         => None
        case PVar(_)            => Some(wilds(c.arity) ++ row.tail)
    }
  // Default matrix: rows with a wildcard in the first column, first column dropped.
  def default(rows: List[Row]): List[Row] =
    rows.collect { case (PVar(_) :: tail) => tail }

  def rootCtors(rows: List[Row]): Set[String] =
    rows.collect { case (PCon(c, _) :: _) => c }.toSet

  // Returns uncovered example rows (empty == exhaustive). `types` are the ADT
  // names of the current columns.
  def missing(reg: Registry, rows: List[Row], types: List[String]): List[Row] =
    if types.isEmpty then
      if rows.isEmpty then List(Nil) else Nil   // empty vector uncovered iff no rows
    else
      val t0 = types.head
      val sigma = reg.adt(t0).ctors
      val used = rootCtors(rows)
      val isComplete = sigma.forall(c => used.contains(c.name))
      if isComplete then
        sigma.flatMap { c =>
          missing(reg, specialize(rows, c), c.argTypes ++ types.tail).map { sub =>
            PCon(c.name, sub.take(c.arity)) :: sub.drop(c.arity)
          }
        }
      else
        val sub = missing(reg, default(rows), types.tail)
        val missingCtor = sigma.find(c => !used.contains(c.name)).get
        sub.map(r => PCon(missingCtor.name, wilds(missingCtor.arity)) :: r)

  // ── (4) Decision-trie emission ────────────────────────────────────────────
  // The output the recursive proof generators consume. An *occurrence* is a path
  // of argument indices from the scrutinee root; it names a sub-position of the
  // input. `Switch(occ, adt, cases)` is "run `adt.elim` on the value at `occ`,
  // branching over every constructor" — exactly the LeftOr-over-elim / LeftExists
  // step of the coverage proof. `Leaf` is a matched clause together with the map
  // from its user binders to the occurrences they denote.
  type Occ = List[Int]
  def occName(o: Occ): String = if o.isEmpty then "x" else "x." + o.mkString(".")

  final case class Col(occ: Occ, adt: String)
  final case class Crow(pats: List[Pat], clause: Int, binds: List[(String, Occ)])

  enum Tree:
    case Switch(occ: Occ, adt: String, cases: List[(String, Tree)])
    case Leaf(clause: Int, binds: List[(String, Occ)], alsoMatched: List[Int])
    case Fail(occ: Occ, missingCtors: List[String])   // a gap: non-exhaustive
  import Tree.*

  def compileTree(reg: Registry, cols: List[Col], rows: List[Crow]): Tree =
    // index of the leftmost column some row destructures with a constructor
    val switchCol = cols.indices.find(j => rows.exists(_.pats(j) match
      case PCon(_, _) => true
      case _          => false))
    switchCol match
      case None =>
        // every remaining column is a binder/wildcard: the first row matches.
        rows match
          case Nil => Fail(Nil, Nil)   // unreachable for exhaustive input
          case r :: rest =>
            val extra = cols.zip(r.pats).collect {
              case (Col(o, _), PVar(n)) if n != "_" => (n, o)
            }
            Leaf(r.clause, r.binds ++ extra, rest.map(_.clause))
      case Some(j) =>
        val col   = cols(j)
        val sigma = reg.adt(col.adt).ctors
        val cases = sigma.map { c =>
          val subCols = c.argTypes.zipWithIndex.map((t, i) => Col(col.occ :+ i, t))
          val newCols = cols.patch(j, subCols, 1)
          val subRows = rows.flatMap { r =>
            r.pats(j) match
              case PCon(c.name, args) =>
                Some(r.copy(pats = r.pats.patch(j, args, 1)))
              case PCon(_, _) => None
              case PVar(n) =>
                val nb = if n != "_" then r.binds :+ (n -> col.occ) else r.binds
                Some(r.copy(pats = r.pats.patch(j, wilds(c.arity), 1), binds = nb))
          }
          val sub = if subRows.isEmpty then Fail(col.occ, List(c.name))
                    else compileTree(reg, newCols, subRows)
          (c.name, sub)
        }
        Switch(col.occ, col.adt, cases)

  def renderTree(t: Tree, indent: String = "    "): String = t match
    case Leaf(clause, binds, also) =>
      val b = if binds.isEmpty then ""
              else "  {" + binds.map((n, o) => s"$n = ${occName(o)}").mkString(", ") + "}"
      val o = if also.isEmpty then ""
              else s"   ⚠ also matches clause(s) ${also.mkString(", ")} (overlap)"
      s"→ clause $clause$b$o"
    case Fail(occ, cs) =>
      s"✗ GAP at ${occName(occ)} (missing ${cs.mkString(", ")})"
    case Switch(occ, adt, cases) =>
      val header = s"elim ${occName(occ)} : $adt"
      val lines = cases.map { (cname, sub) =>
        val body = renderTree(sub, indent + "    ")
        s"$indent├─ $cname  $body"
      }
      header + "\n" + lines.mkString("\n")

  def buildTree(reg: Registry, domain: String, clauses: List[Pat]): Tree =
    val rows = clauses.zipWithIndex.map((p, i) => Crow(List(p), i, Nil))
    compileTree(reg, List(Col(Nil, domain)), rows)

  // ── (5) Proof-step emitters (LISA-style tactic trace) ─────────────────────
  // These fold the trie / clause set into the proof scripts the semantic layer
  // would generate. They emit a *trace* (not compiling LISA) using the real
  // tactic and theorem vocabulary, so the proof shape is concrete and reviewable.

  // Name of the value sitting at an occurrence: the scrutinee `x` at the root,
  // an introduced witness `a<path>` deeper down.
  def witness(o: Occ): String = if o.isEmpty then "x" else "a" + o.mkString("")
  def head(p: Pat): String = p match { case PCon(c, _) => c; case PVar(n) => n }

  // -- Coverage: ∀ x :: domain, caseCoverage(x) -------------------------------
  // Walks the trie. Each Switch becomes an `elim` instantiation + LeftOr over
  // constructors + LeftExists of each constructor's arguments; each Leaf closes
  // the goal by RightExists over the clause binders.
  def emitCoverage(reg: Registry, domain: String, t: Tree): List[String] =
    val out = scala.collection.mutable.ListBuffer[String]()
    def go(t: Tree, ind: String, xExpr: String): Unit = t match
      case Switch(occ, adt, cases) =>
        val s = witness(occ)
        val from = if occ.isEmpty then "the domain assumption" else "the parent constructor's argument typing"
        out += s"${ind}have($s :: $adt)                       // from $from"
        out += s"${ind}val d_${tag(occ)} = InstantiateForall($s)($adt.elim)"
        out += s"$ind  //   ⊢ $s :: $adt ==> " +
               cases.map((c, _) => existsForm(reg, adt, c, occ)).mkString("  ∨  ")
        out += s"${ind}// LeftOr over the ${cases.size} constructor case(s) of $adt:"
        cases.foreach { (cname, sub) =>
          val ct = reg.ctor(adt, cname).get
          val argOccs  = ct.argTypes.indices.map(i => occ :+ i).toList
          val argTerms = argOccs.map(witness)
          val applied  = if ct.arity == 0 then cname else s"$cname(${argTerms.mkString(", ")})"
          out += s"${ind}┌─ case $cname:"
          if ct.arity > 0 then
            val typings = argOccs.zip(ct.argTypes).map((o, ty) => s"${witness(o)} :: $ty").mkString(", ")
            out += s"$ind│    LeftExists ⇒ fresh ${argTerms.mkString(", ")}   with  $typings"
          out += s"$ind│    have($s === $applied)               // this branch's elim disjunct"
          go(sub, s"$ind│    ", xExpr.replaceAll(java.util.regex.Pattern.quote(s) + "\\b", applied))
        }
      case Leaf(clause, binds, also) =>
        if also.nonEmpty then
          out += s"${ind}// ⚠ clauses ${also.mkString(", ")} also reach here — NON-disjoint, proof would not close"
        out += s"${ind}// every position resolved ⇒ clause $clause fires"
        out += s"${ind}have(x === $xExpr)  by Congruence   // chain the (· === c(args)) equalities"
        val bs = if binds.isEmpty then "no binders"
                 else binds.map((n, o) => s"$n := ${witness(o)}").mkString(", ")
        out += s"${ind}have(caseCoverage(x))  by RightExists[$bs] + Tautology   // clause $clause premise holds"
      case Fail(occ, miss) =>
        out += s"${ind}// GAP at ${witness(occ)}: ${miss.mkString(", ")} unmatched — caseCoverage UNPROVABLE"
    out += s"Lemma( ∀ x :: $domain, caseCoverage(x) ) {"
    out += s"  assume x :: $domain"
    go(t, "  ", "x")
    out += s"  thenHave(∀ x :: $domain, caseCoverage(x)) by RightForall"
    out += s"}"
    out.toList

  def tag(o: Occ): String = if o.isEmpty then "root" else o.mkString("")
  def existsForm(reg: Registry, adt: String, cname: String, occ: Occ): String =
    val ct = reg.ctor(adt, cname).get
    val s = witness(occ)
    if ct.arity == 0 then s"($s === $cname)"
    else
      val vs = ct.argTypes.indices.map(i => s"b$i").mkString(", ")
      s"(∃ $vs. wellTyped ∧ $s === $cname($vs))"
  // Pretty single-line reconstruction placeholder for the leaf.
  def reconstruct(reg: Registry, domain: String): String = "c(a…)"

  // -- Incompatible: pairwise disjointness ------------------------------------
  // Walks two patterns to their first divergence: each shared constructor head
  // is peeled by that constructor's injectivity; at the first differing head the
  // tag disequality closes the goal.
  def divergePath(p: Pat, q: Pat): Option[List[Int]] = (p, q) match
    case (PCon(c, _), PCon(d, _)) if c != d => Some(Nil)
    case (PCon(_, as), PCon(_, bs)) =>
      as.lazyZip(bs).zipWithIndex.iterator
        .map { case ((a, b), i) => divergePath(a, b).map(i :: _) }
        .collectFirst { case Some(path) => path }
    case _ => None   // a variable position — compatible, no divergence

  def emitIncompatible(reg: Registry, i: Int, pi: Pat, j: Int, pj: Pat): List[String] =
    val out = scala.collection.mutable.ListBuffer[String]()
    out += s"Lemma( premise_$i ∧ premise_$j ==> ¬(in_$i === in_$j) )   // clauses ${show(pi)}  vs  ${show(pj)}"
    out += s"  assume in_$i === in_$j"
    divergePath(pi, pj) match
      case None =>
        out += s"  // patterns are COMPATIBLE — no disequality exists (would need priority)"
      case Some(path) =>
        var ci = pi; var cj = pj; var occ: Occ = Nil
        path.foreach { step =>
          val c = head(ci)
          out += s"  have(args of $c equal at ${witness(occ)}) by $c.injectivity"
          out += s"    //   from ${show(ci)} === ${show(cj)}  ⊢  componentwise equality; follow arg $step"
          ci = ci.asInstanceOf[PCon].args(step)
          cj = cj.asInstanceOf[PCon].args(step)
          occ = occ :+ step
        }
        out += s"  have(¬(${show(ci)} === ${show(cj)})) by constructorTagDisequality   // tag(${head(ci)}) ≠ tag(${head(cj)}) via Pair.extensionality"
        out += s"  have(⊥) by Tautology   // contradicts equality propagated to ${witness(occ)}"
    out += "}"
    out.toList

  // ── Top-level verdict for a `fun` over `domain` ───────────────────────────
  final case class Verdict(name: String, domain: String, clauses: List[Pat]):
    def report(reg: Registry): String =
      val sb = StringBuilder()
      sb ++= s"━━ $name : $domain ━━\n"
      clauses.foreach(c => sb ++= s"    | ${show(c)}\n")

      val tErrs = clauses.flatMap(c => typeErrors(reg, c, domain))
      val overlaps =
        for
          (a, i) <- clauses.zipWithIndex
          (b, j) <- clauses.zipWithIndex
          if i < j && compatible(a, b)
        yield (a, b)
      val uncovered = missing(reg, clauses.map(List(_)), List(domain))

      if tErrs.nonEmpty then
        sb ++= "  ✗ ill-formed:\n"
        tErrs.foreach(e => sb ++= s"      - $e\n")
      if overlaps.nonEmpty then
        sb ++= "  ✗ NOT disjoint (would need priority):\n"
        overlaps.foreach((a, b) =>
          sb ++= s"      - ${show(a)}  overlaps  ${show(b)}   e.g. ${show(meet(a, b))}\n")
      if uncovered.nonEmpty then
        sb ++= "  ✗ NOT exhaustive; uncovered example(s):\n"
        uncovered.foreach(r => sb ++= s"      - ${showRow(r)}\n")

      if tErrs.isEmpty && overlaps.isEmpty && uncovered.isEmpty then
        sb ++= "  ✓ IN SCOPE  (well-formed, disjoint, exhaustive)\n"
      else
        sb ++= "  ⇒ REJECTED\n"

      // Emit the decision trie whenever the clauses are well-formed: it is the
      // proof-generator input, and it also exhibits any GAP (non-exhaustive) or
      // overlap directly in its structure.
      if tErrs.isEmpty then
        sb ++= "  decision trie (proof skeleton):\n    "
        sb ++= renderTree(buildTree(reg, domain, clauses))
        sb ++= "\n"
      sb.toString

  // ── Example registry ──────────────────────────────────────────────────────
  val reg = Registry(Map(
    "nat"      -> Adt("nat",      List(Ctor("zero", Nil), Ctor("succ", List("nat")))),
    "bool"     -> Adt("bool",     List(Ctor("tru", Nil),  Ctor("fals", Nil))),
    "opt_nat"  -> Adt("opt_nat",  List(Ctor("none", Nil), Ctor("some", List("nat")))),
    "list_nat" -> Adt("list_nat", List(Ctor("nil", Nil),  Ctor("cons", List("nat", "list_nat")))),
  ))

  // Helpers to build nat patterns compactly.
  def z: Pat              = PCon("zero", Nil)
  def s(p: Pat): Pat      = PCon("succ", List(p))
  def k: Pat              = PVar("k")

  val examples = List(
    // isOptionZero : some(zero)/some(succ k) split + none
    Verdict("isOptionZero", "opt_nat", List(
      PCon("none", Nil),
      PCon("some", List(z)),
      PCon("some", List(s(k))))),

    // isGreaterThanOne : depth-1 split on succ's argument
    Verdict("isGreaterThanOne", "nat", List(
      z, s(z), s(s(k)))),

    // isGreaterThanTwo : depth-3 nesting, same head `succ` reused at each level
    Verdict("isGreaterThanTwo", "nat", List(
      z, s(z), s(s(z)), s(s(s(k))))),

    // NEGATIVE 1 — missing the zero branch (non-exhaustive)
    Verdict("missingZero", "nat", List(
      s(z), s(s(k)))),

    // NEGATIVE 2 — catch-all overlaps a specific branch (needs priority)
    Verdict("overlapping", "nat", List(
      z, s(z), s(k))),

    // NEGATIVE 3 — ill-formed: wrong constructor at a nested position
    Verdict("illFormed", "nat", List(
      z, s(PCon("tru", Nil)))),

    // BONUS — list: match on first two elements, catch the rest
    Verdict("listHead2", "list_nat", List(
      PCon("nil", Nil),
      PCon("cons", List(PVar("h"), PCon("nil", Nil))),
      PCon("cons", List(PVar("h"), PCon("cons", List(PVar("h2"), PVar("t"))))))),
  )

  // Print full proof sketches for a chosen in-scope example.
  def printProofs(v: Verdict): Unit =
    println(s"\n══════════ PROOF SKETCH: ${v.name} : ${v.domain} ══════════")
    println("── coverage ──")
    emitCoverage(reg, v.domain, buildTree(reg, v.domain, v.clauses)).foreach(println)
    println("\n── incompatible (same-head pairs only) ──")
    val idx = v.clauses.zipWithIndex
    for
      (pi, i) <- idx; (pj, j) <- idx
      if i < j && head(pi) == head(pj)        // cross-constructor pairs are the trivial root case
    do emitIncompatible(reg, i, pi, j, pj).foreach(println)

  @main def run(): Unit =
    examples.foreach(v => println(v.report(reg)))
    List("isGreaterThanTwo", "isOptionZero").foreach(n =>
      printProofs(examples.find(_.name == n).get))
