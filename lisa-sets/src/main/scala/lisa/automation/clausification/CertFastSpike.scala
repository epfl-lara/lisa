package lisa.automation.clausification

import lisa.automation.clausification.Clausification.Problem
import lisa.kernel.proof.SCProofChecker.checkSCProof
import lisa.utils.K.{_, given}

/** Kernel-check harness for [[CertifiedFastClausifier]]: clausify with a `Sorry` refuter (so every *non-Sorry*
 *  clausification step is validated by the kernel) and print the judgement. */
object CertFastSpike:

  private def pv(i: Int): Variable = Variable(Identifier(s"p$i", 0), Prop)
  private val Q = Variable(Identifier("Rq", 0), Ind >>: Prop) // NOT "P"/"Q": those collide with the prenex schema vars
  private def xv(i: Int): Variable = Variable(Identifier(s"x$i", 0), Ind)

  // Contract: the prover proper must conclude the EMPTY sequent `⊢` (see Clausification.certifyClausal).
  private def refuteWithSorry(problem: Problem): SCProof =
    SCProof(IndexedSeq(Sorry(Sequent(Set.empty, Set.empty))), problem.imports)

  private def check(name: String, phi: Expression): Unit =
    val problem = Problem(Seq(() |- phi), None)
    val proof = CertifiedFastClausifier.certifyClausal(problem, refuteWithSorry)
    val judge = checkSCProof(proof)
    println(s"=== $name ===")
    println(s"  formula: ${phi.repr}")
    println(s"  kernel valid: ${judge.isValid}")
    judge match
      case p: lisa.kernel.proof.SCProofCheckerJudgement.SCInvalidProof =>
        println(s"  path: ${p.path}")
        println(s"  message: ${p.message}")
        // Navigate to the failing step and print it + its premises' bots.
        def nav(pf: SCProof, path: List[Int]): Unit = path match
          case i :: Nil =>
            val st = pf.steps(i)
            println(s"  STEP: ${st.getClass.getSimpleName}  premises=${st.premises}")
            println(s"  step.bot: ${st.bot.repr}")
            st.premises.foreach(pr => println(s"    premise $pr bot: ${(if pr >= 0 then pf.steps(pr).bot else pf.imports(-pr - 1)).repr}"))
          case i :: rest => pf.steps(i) match { case SCSubproof(sp, _) => nav(sp, rest); case s => println(s"  (non-subproof at $i: ${s.getClass.getSimpleName})") }
          case Nil => ()
        nav(proof, p.path.toList)
      case _ => ()

  // Diagnostic: `CertFastSpike diff <file.p>` — find the first formula where certified ≠ fast naming and print both.
  private def diffFile(path: String): Unit =
    import lisa.tptp.KernelParser.{axiomLikeRoles, problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}
    val parsed = problemToKernel(new java.io.File(path))(using (strictMapAtom, strictMapTerm, strictMapVariable))
    val formulas = parsed.formulas.collect {
      case f: lisa.tptp.AnnotatedFormula if axiomLikeRoles.contains(f.role) => f.formula
      case f: lisa.tptp.AnnotatedFormula if f.role == "conjecture"          => neg(f.formula)
    }
    formulas.find(phi => !CertifiedFastClausifier.sameNaming(phi)) match
      case None => println("no divergence")
      case Some(phi) =>
        val fast = CertifiedFastClausifier.canonicalizeNamingAtoms(FastClausify.namedFormula(phi, FastClausify.DefaultThreshold, Clausification.Counter()))
        val cert = CertifiedFastClausifier.canonicalizeNamingAtoms(CertifiedFastClausifier.namedFormula(phi, FastClausify.DefaultThreshold))
        println(s"DIVERGING FORMULA:\n  ${phi.repr}")
        println(s"FAST named:\n  ${fast.repr}")
        println(s"CERT named:\n  ${cert.repr}")

  // Opaque ε-abstraction (mirrors CertifiedFastEquivalenceTest.absEps): replace each raw ε-term by a fresh
  // nullary/function symbol over its Ind free vars, never descending into ε bodies.
  private def absEps(e: Expression): Expression =
    var n = 0
    val memo = scala.collection.mutable.HashMap.empty[Expression, Expression]
    def go(e: Expression): Expression = e match
      case eps @ Application(f0, _) if f0 == epsilon =>
        memo.getOrElseUpdate(eps, {
          val fv = eps.freeVariables.toSeq.filter(_.sort == Ind).sortBy(v => (v.id.name, v.id.no))
          val fSym = Constant(Identifier(s"Feps$n", 0), fv.foldRight(Ind: Sort)((v, acc) => v.sort -> acc))
          n += 1
          fv.foldLeft(fSym: Expression)((acc, v) => acc(v))
        })
      case Application(f, a) => Application(go(f), go(a))
      case Lambda(x, b)      => Lambda(x, go(b))
      case _                 => e
    go(e)

  // Same forward-Skolem / bijection-variable iso as CertifiedFastEquivalenceTest.isoMismatch.
  private def isoMismatch(x: Expression, y: Expression): Option[(Expression, Expression)] =
    val fwd = scala.collection.mutable.HashMap.empty[Expression, Expression]
    val bwd = scala.collection.mutable.HashMap.empty[Expression, Expression]
    def isSk(e: Expression): Boolean = e match
      case c: Constant => c.id.name.startsWith("sK") || c.id.name.startsWith("Feps")
      case _           => false
    def ren(e: Expression): Boolean = e.isInstanceOf[Variable] || isSk(e)
    def go(a: Expression, b: Expression): Option[(Expression, Expression)] = (a, b) match
      case (Application(f1, a1), Application(f2, a2)) => go(f1, f2).orElse(go(a1, a2))
      case (Lambda(_, _), _) | (_, Lambda(_, _))     => if a == b then None else Some((a, b))
      case _ if isSk(a) && isSk(b)                   => if fwd.getOrElseUpdate(a, b) == b then None else Some((a, b))
      case _ if ren(a) && ren(b)                     => if fwd.getOrElseUpdate(a, b) == b && bwd.getOrElseUpdate(b, a) == a then None else Some((a, b))
      case _                                         => if a == b then None else Some((a, b))
    go(x, y)

  // Diagnostic: `CertFastSpike skolemdiff <file.p>` — print, for the first input formula whose fast and certified
  // Skolemizations differ, both the raw ε-form and the fast form (truncated) plus symbol counts.
  private def skolemDiffFile(path: String): Unit =
    import lisa.tptp.KernelParser.{axiomLikeRoles, problemToKernel, strictMapAtom, strictMapTerm, strictMapVariable}
    val parsed = problemToKernel(new java.io.File(path))(using (strictMapAtom, strictMapTerm, strictMapVariable))
    val formulas = parsed.formulas.collect {
      case f: lisa.tptp.AnnotatedFormula if axiomLikeRoles.contains(f.role) => f.formula
      case f: lisa.tptp.AnnotatedFormula if f.role == "conjecture"          => neg(f.formula)
    }
    def cnt(e: Expression, name: String): Int = e.repr.sliding(name.length).count(_ == name)
    formulas.zipWithIndex.foreach { (phi, i) =>
      val fastSk = CertifiedFastClausifier.fastNamedNnfSkolem(phi)
      val rawEps = CertifiedFastClausifier.namedNnfSkolemEps(phi)
      val certSk = CertifiedFastClausifier.stripForall(absEps(rawEps))
      isoMismatch(fastSk, certSk) match
        case None => ()
        case Some(mm) =>
          println(s"=== formula #$i — first mismatch: $mm ===")
          val dir = "/tmp/claude-1001/-home-sguilloud-Work-Lisa-superposition-lisa/56bd4d97-4a71-49e5-b829-03f277814df1/scratchpad"
          java.nio.file.Files.writeString(java.nio.file.Paths.get(s"$dir/sk_fast.txt"), fastSk.repr)
          java.nio.file.Files.writeString(java.nio.file.Paths.get(s"$dir/sk_raweps.txt"), rawEps.repr)
          java.nio.file.Files.writeString(java.nio.file.Paths.get(s"$dir/sk_cert.txt"), certSk.repr)
          println(s"  wrote sk_fast.txt / sk_raweps.txt / sk_cert.txt (lens: ${fastSk.repr.length}/${rawEps.repr.length}/${certSk.repr.length})")
          return
    }
    println("no repr difference in any formula")

  def main(args: Array[String]): Unit =
    if args.headOption.contains("diff") then { diffFile(args(1)); return }
    if args.headOption.contains("skolemdiff") then { skolemDiffFile(args(1)); return }
    // (1) top-level nested Iff chain — naming with no enclosing binders.
    check("iff-chain-5", (1 to 5).map(pv).reduceRight((a, b) => a <=> b))
    // (2) the same chain under a universal — exercises the under-binder HO substitution.
    check("iff-chain-under-forall", forall(Lambda(xv(1), or((1 to 5).map(pv).reduceRight((a, b) => a <=> b))(Q(xv(1))))))
    // (3) an Iff whose child itself contains a quantifier — discharge instantiates d to a quantified formula.
    check("iff-with-quantified-child",
      ((forall(Lambda(xv(1), Q(xv(1)))) <=> pv(2)) <=> (pv(3) <=> pv(4))) <=> pv(5))
