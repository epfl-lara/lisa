package lisa.tptp

import leo.datastructures.TPTP
import leo.datastructures.TPTP.CNF
import leo.datastructures.TPTP.FOF
import leo.modules.input.{TPTPParser => Parser}
import lisa.tptp._
import lisa.utils.K
import lisa.utils.KernelHelpers._
import lisa.utils.KernelHelpers.given_Conversion_String_Identifier

import java.io.File

object KernelParser {
  type DefContext = (String => Option[K.Expression])
  val emptyctx: DefContext = _ => None

  private case class ProblemMetadata(file: String, domain: String, problem: String, status: String, spc: Seq[String])

  /**
   * @param formula A formula in the tptp language
   * @return the corresponding LISA formula
   */
  def parseToKernel(formula: String)(using defctx: DefContext, maps: ((String, Int) => K.Expression, (String, Int) => K.Expression, String => K.Variable)): K.Expression = convertToKernel(
    Parser.fof(formula)
  )(using defctx, (strictMapAtom, strictMapTerm, strictMapVariable))

  /**
   * @param formula a tptp formula in leo parser
   * @return the same formula in LISA
   */
  def convertToKernel(formula: FOF.Formula)(using defctx: DefContext, maps: ((String, Int) => K.Expression, (String, Int) => K.Expression, String => K.Variable)): K.Expression = {
    val (mapAtom, mapTerm, mapVariable) = maps
    formula match {
      case FOF.AtomicFormula(f, args) =>
        if f == "$true" then K.top
        else if f == "$false" then K.bot
        else if (f.head == '$' && args.size == 0 && defctx(f.tail).isDefined) then defctx(f.tail).get
        else args.foldLeft(mapAtom(f, args.size): K.Expression)((acc, arg) => acc(convertTermToKernel(arg)))

      // else throw new Exception("Unknown atomic formula kind: " + kind +" in " + f)
      case FOF.QuantifiedFormula(quantifier, variableList, body) =>
        quantifier match {
          case FOF.! =>
            variableList.foldRight(convertToKernel(body))((s, f) => K.forall(mapVariable(s), f))
          case FOF.? => variableList.foldRight(convertToKernel(body))((s, f) => K.exists(mapVariable(s), f))
          case FOF.Epsilon => ???
        }
      case FOF.UnaryFormula(connective, body) =>
        connective match {
          case FOF.~ => K.neg(convertToKernel(body))
        }
      case FOF.BinaryFormula(connective, left, right) =>
        connective match {
          case FOF.<=> => convertToKernel(left) <=> convertToKernel(right)
          case FOF.Impl => convertToKernel(left) ==> convertToKernel(right)
          case FOF.<= => convertToKernel(right) ==> convertToKernel(left)
          case FOF.<~> => !(convertToKernel(left) <=> convertToKernel(right))
          case FOF.~| => !(convertToKernel(left) \/ convertToKernel(right))
          case FOF.~& => !(convertToKernel(left) /\ convertToKernel(right))
          case FOF.| => convertToKernel(left) \/ convertToKernel(right)
          case FOF.& => convertToKernel(left) /\ convertToKernel(right)
        }
      case FOF.Equality(left, right) => K.equality(convertTermToKernel(left))(convertTermToKernel(right))
      case FOF.Inequality(left, right) => !K.equality(convertTermToKernel(left))(convertTermToKernel(right))
    }
  }

  def convertToKernel(sequent: FOF.Sequent)(using defctx: DefContext, maps: ((String, Int) => K.Expression, (String, Int) => K.Expression, String => K.Variable)): K.Sequent = {
    K.Sequent(sequent.lhs.map(convertToKernel).toSet, sequent.rhs.map(convertToKernel).toSet)
  }

  def convertToKernel(formula: CNF.Formula)(using defctx: DefContext, maps: ((String, Int) => K.Expression, (String, Int) => K.Expression, String => K.Variable)): K.Expression = {
    K.multior(
      formula.map {
        case CNF.PositiveAtomic(formula) => multiapply(strictMapAtom(formula.f, formula.args.size))(formula.args.map(convertTermToKernel).toList)
        case CNF.NegativeAtomic(formula) => !multiapply(strictMapAtom(formula.f, formula.args.size))(formula.args.map(convertTermToKernel).toList)
        case CNF.Equality(left, right) => K.equality(convertTermToKernel(left))(convertTermToKernel(right))
        case CNF.Inequality(left, right) => !K.equality(convertTermToKernel(left))(convertTermToKernel(right))
      }
    )
  }

  /**
   * @param term a tptp term in leo parser
   * @return the same term in LISA
   */
  def convertTermToKernel(term: CNF.Term)(using defctx: DefContext, maps: ((String, Int) => K.Expression, (String, Int) => K.Expression, String => K.Variable)): K.Expression =
    val (mapAtom, mapTerm, mapVariable) = maps
    term match {
      case CNF.AtomicTerm(f, args) => K.multiapply(mapTerm(f, args.size))(args map convertTermToKernel)
      case CNF.Variable(name) => mapVariable(name)
      // Fix B: a distinct object "..." → a plain nullary constant, `$d`-prefixed to avoid colliding with ordinary
      // functors (the surrounding quotes are stripped so the two occurrences of the same object share a symbol).
      case CNF.DistinctObject(name) => distinctObjectConstant(name)
    }

  /** The kernel constant a distinct object `"name"` is encoded as: a plain nullary constant, `$d`-prefixed so it
   *  cannot collide with an ordinary functor, with the quotes stripped so two occurrences of the same object
   *  share a symbol. One definition, so the conversions above and [[distinctObjectsOf]] cannot disagree about
   *  the encoding — which is why the latter can classify by AST node rather than by testing the prefix back. */
  private def distinctObjectConstant(name: String)(using maps: ((String, Int) => K.Expression, (String, Int) => K.Expression, String => K.Variable)): K.Expression =
    val (_, mapTerm, _) = maps
    mapTerm("$d" + name.stripPrefix("\"").stripSuffix("\""), 0)

  /**
   * @param term a tptp term in leo parser
   * @return the same term in LISA
   */
  def convertTermToKernel(term: FOF.Term)(using defctx: DefContext, maps: ((String, Int) => K.Expression, (String, Int) => K.Expression, String => K.Variable)): K.Expression =
    val (mapAtom, mapTerm, mapVariable) = maps
    term match {
      case FOF.AtomicTerm(f, args) =>
        if (f.head == '$' && args.size == 0 && defctx(f.tail).isDefined) then defctx(f.tail).get
        else K.multiapply(mapTerm(f, args.size))(args map convertTermToKernel)
      case FOF.Variable(name) => mapVariable(name)
      // Fix B: distinct objects and numeric literals → plain nullary constants, prefixed `$d` / `$n` so they never
      // collide with ordinary functors (or each other). No arithmetic/distinctness axioms — sound, just uninterpreted.
      case FOF.DistinctObject(name) => distinctObjectConstant(name)
      case FOF.NumberTerm(value) => mapTerm("$n" + value.pretty, 0)
      case FOF.QuantifiedTerm(quantifier, Seq(x), body) => K.epsilon(mapVariable(x), convertToKernel(body))
      case FOF.QuantifiedTerm(_, _, _) => throw Exception("Only epsilon is supported as term quantifier")
    }

  /**
   * @param formula an annotated tptp statement
   * @return the corresponding LISA formula augmented with name and role.
   */
  def annotatedStatementToKernel(formula: String)(using defctx: DefContext, maps: ((String, Int) => K.Expression, (String, Int) => K.Expression, String => K.Variable)): AnnotatedStatement = {
    val i = Parser.annotatedFOF(formula)
    i match
      case TPTP.FOFAnnotated(name, role, formula, annotations, origin) =>
        formula match {
          case FOF.Logical(formula) => AnnotatedFormula(role, name, convertToKernel(formula), annotations)
          case FOF.Sequent(antecedent, succedent) =>
            AnnotatedSequent(role, name, K.Sequent(antecedent.map(convertToKernel).toSet, succedent.map(convertToKernel).toSet), annotations)
        }

  }

  private def problemToKernel(problemFile: File, md: ProblemMetadata)(using maps: ((String, Int) => K.Expression, (String, Int) => K.Expression, String => K.Variable)): TptpProblem = {
    val (mapAtom, mapTerm, mapVariable) = maps
    val file = io.Source.fromFile(problemFile)
    val folder = problemFile.getParentFile
    val pattern = "SPC\\s*:\\s*[A-z]{3}(_[A-z]{3})*".r
    val g = file.getLines()
    given emptyctx: DefContext = _ => None

    def search(): String = pattern.findFirstIn(g.next()).getOrElse(search())

    val i = Parser.problem(file)
    def problemToFormulas(i: TPTP.Problem): Seq[TPTP.AnnotatedFormula] = {
      val file = io.Source.fromFile(problemFile)
      i.formulas ++ i.includes.flatMap(i => {
        val probFile = new File(folder, i._1)
        val file = if (!probFile.exists) then
          val tptpEnv = sys.env.getOrElse("TPTP", "")
          if (tptpEnv.isEmpty) throw new Exception("TPTP environment variable not set, and file " + i._1 + " does not exist.")
          val probFile = new File(tptpEnv, i._1)
          if (!probFile.exists) throw new Exception("File " + i._1 + " does not exist in TPTP environment variable " + tptpEnv + " nor in " + folder.getPath)
          io.Source.fromFile(probFile)
        else io.Source.fromFile(probFile)
        problemToFormulas(Parser.problem(file))
      })
    }
    val iformulas = problemToFormulas(i)
    val sq = iformulas map {
      case TPTP.FOFAnnotated(name, role, formula, annotations, origin) =>
        formula match {
          case FOF.Logical(formula) => AnnotatedFormula(role, name, convertToKernel(formula), annotations)
          case FOF.Sequent(antecedent, succedent) =>
            AnnotatedSequent(role, name, K.Sequent(antecedent.map(convertToKernel).toSet, succedent.map(convertToKernel).toSet), annotations)
        }
      case TPTP.CNFAnnotated(name, role, formula, annotations, origin) =>
        formula match {
          case CNF.Logical(formula) =>
            val inner = convertToKernel(formula)
            val closure = inner.freeVariables.foldLeft(inner)((acc, v) => K.forall(v, acc))
            AnnotatedFormula(role, name, closure, annotations)
        }
      case _ =>
        println("Unknown statement:" + i.pretty)
        throw FileNotAcceptedException("Only FOF formulas are supported", problemFile.getPath)
    }
    TptpProblem(md.file, md.domain, md.problem, md.status, md.spc, sq, distinctObjectsOf(iformulas))
  }

  /** The distinct objects occurring anywhere in `statements`, as the kernel constants they are encoded as, in
   *  first-occurrence order.
   *
   *  Collected from the parsed TPTP tree, so a distinct object is one the grammar says is one — a
   *  `DistinctObject` node — rather than one whose encoded name happens to begin with `$d`. Numeric literals
   *  are deliberately not included: they are encoded the same way, but `1`, `1.0` and `1/1` can denote the
   *  same number, so asserting them pairwise distinct would be unsound. */
  private def distinctObjectsOf(statements: Seq[TPTP.AnnotatedFormula])(using defctx: DefContext, maps: ((String, Int) => K.Expression, (String, Int) => K.Expression, String => K.Variable)): IndexedSeq[K.Expression] =
    val found = scala.collection.mutable.LinkedHashSet.empty[K.Expression]
    def cnfTerm(t: CNF.Term): Unit = t match
      case CNF.AtomicTerm(_, args)  => args.foreach(cnfTerm)
      case CNF.DistinctObject(name) => found += distinctObjectConstant(name)
      case _                        => ()
    def cnfFormula(f: CNF.Formula): Unit = f.foreach {
      case CNF.PositiveAtomic(a)    => a.args.foreach(cnfTerm)
      case CNF.NegativeAtomic(a)    => a.args.foreach(cnfTerm)
      case CNF.Equality(l, r)       => cnfTerm(l); cnfTerm(r)
      case CNF.Inequality(l, r)     => cnfTerm(l); cnfTerm(r)
    }
    def fofTerm(t: FOF.Term): Unit = t match
      case FOF.AtomicTerm(_, args)     => args.foreach(fofTerm)
      case FOF.DistinctObject(name)    => found += distinctObjectConstant(name)
      case FOF.QuantifiedTerm(_, _, b) => fofFormula(b)
      case _                           => ()
    def fofFormula(f: FOF.Formula): Unit = f match
      case FOF.AtomicFormula(_, args)      => args.foreach(fofTerm)
      case FOF.QuantifiedFormula(_, _, b)  => fofFormula(b)
      case FOF.UnaryFormula(_, b)          => fofFormula(b)
      case FOF.BinaryFormula(_, l, r)      => fofFormula(l); fofFormula(r)
      case FOF.Equality(l, r)              => fofTerm(l); fofTerm(r)
      case FOF.Inequality(l, r)            => fofTerm(l); fofTerm(r)
    statements.foreach {
      case TPTP.FOFAnnotated(_, _, FOF.Logical(f), _, _)               => fofFormula(f)
      case TPTP.FOFAnnotated(_, _, FOF.Sequent(lhs, rhs), _, _)        => lhs.foreach(fofFormula); rhs.foreach(fofFormula)
      case TPTP.CNFAnnotated(_, _, CNF.Logical(f), _, _)               => cnfFormula(f)
      case _                                                           => ()
    }
    found.toIndexedSeq

  /**
   * @param problemFile a file containning a tptp problem
   * @return a TptpProblem object containing the data of the tptp problem in LISA representation
   */
  def problemToKernel(problemFile: File)(using maps: ((String, Int) => K.Expression, (String, Int) => K.Expression, String => K.Variable)): TptpProblem = {
    problemToKernel(problemFile, getProblemInfos(problemFile))
  }

  /**
   * @param problemFile a path to a file containing a tptp problem
   * @return a TptpProblem object containing the data of the tptp problem in LISA representation
   */
  def problemToKernel(problemFile: String)(using maps: ((String, Int) => K.Expression, (String, Int) => K.Expression, String => K.Variable)): TptpProblem = {
    problemToKernel(File(problemFile))
  }

  val axiomLikeRoles = Set("axiom", "hypothesis", "definition", "assumption", "lemma", "theorem", "corollary", "negated_conjecture")

  /**
   * Given a problem consisting of many axioms and a single conjecture, create a sequent with axioms on the left
   * and conjecture on the right.
   *
   * @param problem a problem, containing a list of annotated formulas from a tptp file
   * @return a sequent with axioms of the problem on the left, and the conjecture on the right
   */
  def problemToSequent(problem: TptpProblem): K.Sequent = {
    if (problem.spc.contains("CNF")) problem.formulas.map(_.asInstanceOf[AnnotatedFormula].formula) |- ()
    else
      problem.formulas.foldLeft[K.Sequent](() |- ())((s, f) =>
        if (axiomLikeRoles.contains(f.role)) s +<< f.asInstanceOf[AnnotatedFormula].formula
        else if (f.role == "conjecture" && s.right.isEmpty) s +>> f.asInstanceOf[AnnotatedFormula].formula
        else throw Exception("Can only agglomerate axioms and one conjecture into a sequents")
      )
  }

  def sanitize(s: String) =
    // Fix A: fold the whole identifier — numeric suffix included — into the *name*; never keep a trailing
    // `_<digits>`. The String→Identifier conversion parses such a suffix into `Identifier.no` (an `Int`), which
    // overflows on big SUMO ids like `c_bcase_3235139646`. `unsanitize` reverses `$u`/`$s` and ignores `no`, so
    // escaping every `_` as `$u` round-trips just as well while keeping the whole id in the (unbounded) name.
    s.split("_").mkString("$u").replace(" ", "$s")

  def unsanitize(s: String, no: Int): String =
    val r1 = s.replace("$u", "_").replace("$s", " ")
    // if r1.contains(" ") then s"'$r1'" else r1
    r1
  def unsanitize(id: K.Identifier): String =
    unsanitize(id.name, id.no)

  val strictMapAtom: ((String, Int) => K.Expression) = (f, n) =>
    val kind = f.head
    val id = f.tail
    if f(0).isUpper then K.Variable(sanitize(f), K.predicateType(n))
    else K.Constant(sanitize(f), K.predicateType(n))
  val strictMapTerm: ((String, Int) => K.Expression) = (f, n) =>
    val kind = f.head
    val id = f.tail
    if f(0).isUpper then K.Variable(sanitize(f), K.functionType(n))
    else K.Constant(sanitize(f), K.functionType(n))
  val strictMapVariable: (String => K.Variable) = f => K.Variable(sanitize(f), K.Ind)

  /**
   * Given a folder containing folders containing problem (typical organisation of TPTP library) and a list of spc,
   * return the same arrangement of problems in LISA syntax, filtered so that only problems with at least one
   * spc from the "spc" argument.
   *
   * @param spc  a list of 3-characters codes representing properties of a problem, such as FOF for First Order Logic.
   * @param path the path to the tptp library.
   * @return A sequence of domains, each being a sequence of problems
   */
  def gatherAllTPTPFormulas(spc: Seq[String], path: String): Seq[Seq[TptpProblem]] = {
    val d = new File(path)
    val probfiles: Array[File] = if (d.exists) {
      if (d.isDirectory) {
        if (d.listFiles().isEmpty) println("empty directory")
        d.listFiles.filter(_.isDirectory)

      } else throw new Exception("Specified path is not a directory.")
    } else throw new Exception("Specified path does not exist.")

    probfiles.map(d => gatherFormulas(spc, d.getPath)).toSeq
  }

  def gatherFormulas(spc: Seq[String], path: String): Seq[TptpProblem] = {
    val d = new File(path)
    val probfiles: Array[File] = if (d.exists) {
      if (d.isDirectory) {
        if (d.listFiles().isEmpty) println("empty directory")
        d.listFiles.filter(_.isFile)

      } else throw new Exception("Specified path is not a directory.")
    } else throw new Exception("Specified path does not exist.")

    val r = probfiles.foldRight(List.empty[TptpProblem])((p, current) => {
      val md = getProblemInfos(p)
      if (md.spc.exists(spc.contains)) problemToKernel(p, md)(using (strictMapAtom, strictMapTerm, strictMapVariable)) :: current
      else current
    })
    r
  }

  /**
   * @param file a file containing a tptp problem
   * @return the metadata info (file name, domain, problem, status and spc) in the file
   */
  private def getProblemInfos(file: File): ProblemMetadata = {
    val pattern = "((File)|(Domain)|(Problem)|(Status)|(SPC))\\s*:.*".r
    val s = io.Source.fromFile(file)
    val g = s.getLines()
    var fil: String = "?"
    var dom: String = "?"
    var pro: String = "?"
    var sta: String = "?"
    var spc: Seq[String] = Seq()

    val count: Int = 0
    while (g.hasNext && count < 5) {
      val line = g.next()
      val res = pattern.findFirstIn(line)
      if (res.nonEmpty) {
        val act = res.get
        if (act(0) == 'F') fil = act.drop(act.indexOf(":") + 2)
        else if (act(0) == 'D') dom = act.drop(act.indexOf(":") + 2)
        else if (act(0) == 'P') pro = act.drop(act.indexOf(":") + 2)
        else if (act(1) == 't') sta = act.drop(act.indexOf(":") + 2)
        else if (act(1) == 'P') spc = act.drop(act.indexOf(":") + 2).split("_").toIndexedSeq
      }
    }
    s.close()
    ProblemMetadata(fil, dom, pro, sta, spc)
  }

}
