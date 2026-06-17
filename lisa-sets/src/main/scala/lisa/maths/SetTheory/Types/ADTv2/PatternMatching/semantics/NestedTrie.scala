package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADTv2.interface.ADT
import lisa.maths.SetTheory.Types.ADTv2.interface.Constructor
import lisa.maths.SetTheory.Types.TypingHelpers

/**
 * Real-typed port of the prototype trie compiler for multi-level nested patterns
 * (see scratch/NestedPatternChecker.scala). Pure: it inspects the live
 * `ADT`/`Constructor` interface objects and the `Expr[Ind]` arguments coming out
 * of `CaseAccumulator`, and decides whether a `Case` set is in scope for the
 * proposed (exhaustive, non-overlapping) nested-pattern system. It produces no
 * proofs — it emits the decision trie that the coverage / incompatible proof
 * generators would consume.
 */
private[semantics] object NestedTrie {

  // ── Pattern AST ────────────────────────────────────────────────────────────
  enum Pat:
    case PVar(name: String)
    case PCon(ctor: String, args: List[Pat])
  import Pat.*

  type Occ = List[Int]
  def occName(o: Occ): String = if o.isEmpty then "x" else "x." + o.mkString(".")
  def wilds(n: Int): List[Pat] = List.fill(n)(PVar("_"))

  def show(p: Pat): String = p match
    case PVar(n) => n
    case PCon(c, Nil) => c
    case PCon(c, args) => s"$c(${args.map(show).mkString(", ")})"

  // ── Decision trie (the proof-generator input) ──────────────────────────────
  enum Tree:
    case Switch(occ: Occ, adt: String, cases: List[(String, Tree)])
    case Leaf(clause: Int, binds: List[(String, Occ)], alsoMatched: List[Int])
    case Fail(occ: Occ, missing: List[String])
  import Tree.*

  // All registered constructors, keyed by their term-level identifier. Mirrors
  // NestedConstructorPattern.resolveNullaryGuard's global lookup.
  private[semantics] def allConstructors: Seq[Constructor[?]] =
    ADT.allADTs.toSeq.flatMap(_.constructors)

  // Peel a set-application spine `c * a0 * a1 * …` (built by the `*` DSL operator,
  // i.e. nested `app(...)`) into its head and value arguments, using the `*`
  // extractor from TypingHelpers.
  private[semantics] def peelApp(t: Expr[Ind]): (Expr[Ind], List[Expr[Ind]]) =
    TypingHelpers.`*`.unapply(t) match
      case Some((f, x)) => val (h, as) = peelApp(f); (h, as :+ x)
      case None => (t, Nil)

  // ── Parse an Expr[Ind] argument into a Pat ─────────────────────────────────
  // A variable becomes a binder; a constructor application becomes a PCon. The
  // head is the constructor symbol (optionally applied to type args); we keep
  // only the constructor's value arity (rightmost args).
  def parsePat(term: Expr[Ind]): Pat =
    val (h, valueArgs) = peelApp(term)
    val headSym = h match { case Multiapp(hd, _) => hd }
    headSym match
      case c: Constant[?] @unchecked =>
        allConstructors.find(_.id == c.id) match
          case Some(ctor) =>
            val vs = valueArgs.takeRight(ctor.semantic.arity)
            PCon(ctor.name, vs.map(parsePat))
          case None => PVar(term.toString)
      case _ => PVar(term.toString)

  // ── Column model carrying the resolved ADT + its type arguments ────────────
  final case class Col(occ: Occ, ty: Option[(ADT[?], Seq[Expr[Ind]])])
  final case class Crow(pats: List[Pat], clause: Int, binds: List[(String, Occ)])

  // The argument columns introduced when switching on constructor `c` at a column
  // of type (adt, typeArgs): substitute the ADT's type variables by typeArgs into
  // each argument type, then resolve it back to an ADT (None for non-ADT types,
  // e.g. function arguments — those positions can only ever hold binders).
  private def childCols(adt: ADT[?], typeArgs: Seq[Expr[Ind]], c: Constructor[?], occ: Occ): List[Col] =
    val subst = adt.typeVariablesSeq.zip(typeArgs).map((v, a) => v := a)
    c.semantic.semanticSignature2.zipWithIndex.map { case ((_, tyTerm), i) =>
      val concrete = tyTerm.substitute(subst*).asInstanceOf[Expr[Ind]]
      Col(occ :+ i, ADT.unapply(concrete))
    }.toList

  private def ctorsOf(adt: ADT[?]): Seq[Constructor[?]] = adt.constructors

  // ── The compiler (identical control flow to the prototype) ─────────────────
  def compile(cols: List[Col], rows: List[Crow]): Tree =
    val switchCol = cols.indices.find(j =>
      cols(j).ty.isDefined && rows.exists(_.pats(j) match
        case PCon(_, _) => true
        case _ => false)
    )
    switchCol match
      case None =>
        rows match
          case Nil => Fail(Nil, Nil)
          case r :: rest =>
            val extra = cols.zip(r.pats).collect {
              case (Col(o, _), PVar(n)) if n != "_" => (n, o)
            }
            Leaf(r.clause, r.binds ++ extra, rest.map(_.clause))
      case Some(j) =>
        val col = cols(j)
        val (adt, typeArgs) = col.ty.get
        val sigma = ctorsOf(adt)
        val cases = sigma.map { c =>
          val subCols = childCols(adt, typeArgs, c, col.occ)
          val newCols = cols.patch(j, subCols, 1)
          val subRows = rows.flatMap { r =>
            r.pats(j) match
              case PCon(name, args) if name == c.name =>
                Some(r.copy(pats = r.pats.patch(j, args, 1)))
              case PCon(_, _) => None
              case PVar(n) =>
                val nb = if n != "_" then r.binds :+ (n -> col.occ) else r.binds
                Some(r.copy(pats = r.pats.patch(j, wilds(c.semantic.arity), 1), binds = nb))
          }
          val sub =
            if subRows.isEmpty then Fail(col.occ, List(c.name))
            else compile(newCols, subRows)
          (c.name, sub)
        }.toList
        Switch(col.occ, adt.name, cases)

  // Entry point: a `fun`/`recFun` clause set. Each clause is its top constructor
  // plus the value-argument terms (exactly what CaseAccumulator stores).
  def buildTree(
      domainAdt: ADT[?],
      domainTypeArgs: Seq[Expr[Ind]],
      clauses: Seq[(Constructor[?], Seq[Expr[Ind]])]
  ): Tree =
    val rows = clauses.zipWithIndex.map { case ((cons, args), i) =>
      Crow(List(PCon(cons.name, args.map(parsePat).toList)), i, Nil)
    }.toList
    compile(List(Col(Nil, Some((domainAdt, domainTypeArgs)))), rows)

  // ── Rendering ──────────────────────────────────────────────────────────────
  def render(t: Tree, indent: String = "    "): String = t match
    case Leaf(clause, binds, also) =>
      val b =
        if binds.isEmpty then ""
        else "  {" + binds.map((n, o) => s"$n = ${occName(o)}").mkString(", ") + "}"
      val o = if also.isEmpty then "" else s"   ⚠ overlap with clause(s) ${also.mkString(", ")}"
      s"→ clause $clause$b$o"
    case Fail(occ, cs) =>
      s"✗ GAP at ${occName(occ)} (missing ${cs.mkString(", ")})"
    case Switch(occ, adt, cases) =>
      val lines = cases.map((cn, sub) => s"$indent├─ $cn  ${render(sub, indent + "    ")}")
      s"elim ${occName(occ)} : $adt\n" + lines.mkString("\n")

  // ── Verdict scanned straight off the trie ──────────────────────────────────
  def gaps(t: Tree): List[String] = t match
    case Fail(occ, cs) => List(s"${cs.mkString(", ")} unmatched at ${occName(occ)}")
    case Switch(_, _, cases) => cases.flatMap((_, s) => gaps(s))
    case Leaf(_, _, _) => Nil
  def overlaps(t: Tree): List[String] = t match
    case Leaf(c, _, also) if also.nonEmpty => List(s"clauses ${(c :: also).mkString(", ")}")
    case Switch(_, _, cases) => cases.flatMap((_, s) => overlaps(s))
    case _ => Nil

  def analyze(
      name: String,
      domainAdt: ADT[?],
      domainTypeArgs: Seq[Expr[Ind]],
      clauses: Seq[(Constructor[?], Seq[Expr[Ind]])]
  ): String =
    val tree = buildTree(domainAdt, domainTypeArgs, clauses)
    val g = gaps(tree)
    val o = overlaps(tree)
    val sb = StringBuilder()
    sb ++= s"━━ $name : ${domainAdt.name}${if domainTypeArgs.nonEmpty then domainTypeArgs.mkString("[", ", ", "]") else ""} ━━\n"
    clauses.foreach((c, args) => sb ++= s"    | ${c.name}${if args.nonEmpty then args.map(a => show(parsePat(a))).mkString("(", ", ", ")") else ""}\n")
    if g.isEmpty && o.isEmpty then sb ++= "  ✓ IN SCOPE (disjoint, exhaustive)\n"
    else
      if o.nonEmpty then o.foreach(x => sb ++= s"  ✗ overlap (needs priority): $x\n")
      if g.nonEmpty then g.foreach(x => sb ++= s"  ✗ not exhaustive: $x\n")
      sb ++= "  ⇒ REJECTED\n"
    sb ++= "  decision trie:\n    " + render(tree) + "\n"
    sb.toString
}
