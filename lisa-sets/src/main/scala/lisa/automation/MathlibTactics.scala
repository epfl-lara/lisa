package lisa.automation

import lisa.utils.fol.{FOL => F}
import lisa.utils.fol.FOL.{*, given}
import lisa.utils.prooflib.BasicStepTactic.*
import lisa.utils.prooflib.ProofTacticLib.{*, given}
import lisa.utils.prooflib.SimpleDeducedSteps.Restate
import lisa.utils.prooflib.{Library, ProofTacticLib}
import lisa.utils.unification.UnificationUtils
import lisa.utils.unification.UnificationUtils.RewriteContext

/**
 * A small collection of Lean/mathlib-inspired tactics, implemented on top of LISA's proof DSL.
 *
 * These are intentionally lightweight wrappers (not a full re-implementation of Lean tactics).
 */
object MathlibTactics {

  /**
   * `rw`-style rewriting: alias for `Substitution.Apply` with a more Lean-like name.
   *
   * Typical usage:
   *   - `thenHave(goal) by Rw(eq1, eq2, iff1)` (rewrites the previous step)
   *   - `have(goal) by Rw(eq)(someEarlierStep)`
   */
  object Rw extends ProofTactic {
    def apply(using lib: Library, proof: lib.Proof)(
        substitutions: (proof.Fact | F.Expr[F.Prop])*
    )(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
      Substitution.Apply(using lib, proof)(substitutions*)(premise)(bot)
  }

  /**
   * `simp`-style "try easy automation":
   * - first tries rewriting with the provided substitution rules (if any),
   * - then tries `Tautology`, then `Congruence`.
   *
   * This is best-effort and intentionally conservative; it does not do rewriting
   * under binders, simp-normal forms, etc.
   */
  object Simp extends ProofTactic with ProofSequentTactic with ProofFactSequentTactic {

    private def tableauQuiet(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement =
      val prev = Tableau.debug
      Tableau.debug = false
      try Tableau(using lib, proof)(bot)
      finally Tableau.debug = prev

    def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement =
      Tautology(using lib, proof)(bot) match
        case ok: proof.ValidProofTactic => ok
        case _: proof.InvalidProofTactic =>
          Congruence(using lib, proof)(bot) match
            case ok: proof.ValidProofTactic => ok
            case _: proof.InvalidProofTactic =>
              tableauQuiet(using lib, proof)(bot)

    def apply(using lib: Library, proof: lib.Proof)(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
      from(using lib, proof)(premise)(bot)

    def from(using lib: Library, proof: lib.Proof)(premises: proof.Fact*)(bot: F.Sequent): proof.ProofTacticJudgement =
      Tautology.from(using lib, proof)(premises*)(bot) match
        case ok: proof.ValidProofTactic => ok
        case _: proof.InvalidProofTactic =>
          Congruence.from(using lib, proof)(premises*)(bot) match
            case ok: proof.ValidProofTactic => ok
            case _: proof.InvalidProofTactic =>
              val prev = Tableau.debug
              Tableau.debug = false
              try Tableau.from(using lib, proof)(premises*)(bot)
              finally Tableau.debug = prev

    def apply(using lib: Library, proof: lib.Proof)(
        substitutions: (proof.Fact | F.Expr[F.Prop])*
    )(premise: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement =
      if substitutions.isEmpty then from(using lib, proof)(premise)(bot)
      else
        Substitution.Apply(using lib, proof)(substitutions*)(premise)(bot) match
          case ok: proof.ValidProofTactic => ok
          case _: proof.InvalidProofTactic =>
            from(using lib, proof)(premise)(bot)
  }

  /**
   * Lean `by_cases p`: split into two branches `p` and `¬p`, then close using cut with excluded middle.
   *
   * Premises are expected to be proofs of the goal under the additional assumptions `p` and `¬p`.
   */
  object ByCases extends ProofTactic {
    def apply(using lib: Library, proof: lib.Proof)(
        phi: F.Expr[F.Prop]
    )(casePos: proof.Fact, caseNeg: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {

      val pos = proof.getSequent(casePos)
      val neg = proof.getSequent(caseNeg)
      val nphi = F.neg(phi)
      val em = F.or(phi)(nphi)

      val posHasPhi = pos.left.exists(F.isSame(_, phi))
      val negHasNotPhi = neg.left.exists(F.isSame(_, nphi))

      if !posHasPhi then proof.InvalidProofTactic("`ByCases`: first premise does not assume `phi` on the left.")
      else if !negHasNotPhi then proof.InvalidProofTactic("`ByCases`: second premise does not assume `¬phi` on the left.")
      else if !F.isSameSet(pos.right, bot.right) || !F.isSameSet(neg.right, bot.right) then
        proof.InvalidProofTactic("`ByCases`: both branches must conclude the same right-hand side as the goal.")
      else {
        val gamma = bot.left
        val gammaPos = pos.left.filterNot(F.isSame(_, phi))
        val gammaNeg = neg.left.filterNot(F.isSame(_, nphi))

        if !F.isSameSet(gammaPos, gamma) || !F.isSameSet(gammaNeg, gamma) then
          proof.InvalidProofTactic("`ByCases`: both branches must have the goal's left-hand side, plus `phi`/`¬phi` respectively.")
        else
          TacticSubproof {
            import lib.*

            val em0 = have(() |- em) by Tautology
            val emG = have(gamma |- em) by Weakening(em0)

            val split = have((gamma + em) |- bot.right) by LeftOr.withParameters(phi, nphi)(casePos, caseNeg)
            have(bot) by Cut.withParameters(em)(emG, split)
          }
      }
    }
  }

  /**
   * Lean `by_contra h`: prove `phi` by contradiction from a proof of falsity under `¬phi`.
   *
   * Expects a premise proving the empty succedent under the additional assumption `¬phi`.
   * The goal must be a singleton succedent `phi`.
   */
  object ByContra extends ProofTactic {
    def apply(using lib: Library, proof: lib.Proof)(
        phi: F.Expr[F.Prop]
    )(contra: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      val contraSeq = proof.getSequent(contra)
      val nphi = F.neg(phi)
      val nnphi = F.neg(nphi)

      if bot.right.size != 1 || !F.isSame(bot.right.head, phi) then
        return proof.InvalidProofTactic("`ByContra`: goal must have a single formula on the right, equal to `phi`.")
      if contraSeq.right.nonEmpty then
        return proof.InvalidProofTactic("`ByContra`: contradiction premise must have an empty right-hand side.")
      if !contraSeq.left.exists(F.isSame(_, nphi)) then
        return proof.InvalidProofTactic("`ByContra`: contradiction premise must assume `¬phi` on the left.")

      val gamma = bot.left
      val gammaContra = contraSeq.left.filterNot(F.isSame(_, nphi))
      if !F.isSameSet(gammaContra, gamma) then
        return proof.InvalidProofTactic("`ByContra`: contradiction premise must have the goal's left-hand side plus `¬phi`.")

      TacticSubproof {
        import lib.*

        // derive Γ ⊢ ¬¬phi
        have(contraSeq) by Restate.from(contra)
        thenHave(gamma |- nnphi) by RightNot.withParameters(nphi)
        val nnStep = lastStep

        // classical step: ¬¬phi ⊢ phi
        val dn = have(nnphi |- phi) by Tautology
        val dnG = have((gamma + nnphi) |- phi) by Weakening(dn)

        have(bot) by Cut.withParameters(nnphi)(nnStep, dnG)
      }
    }
  }

  /**
   * A goal-directed "Horn-style" solver inspired by Lean's `solve_by_elim`:
   *
   * - Works on singleton goals `Γ ⊢ φ`.
   * - Uses hypotheses in `Γ` as Horn clauses (leading `∀` + right-nested `⇒`).
   * - Instantiates `∀` by matching the clause head against the goal (using LISA's matcher),
   *   then discharges antecedents via recursive calls.
   *
   * This is not complete for first-order logic, but is often effective for
   * "typeclass-like" algebraic reasoning where goals are driven by implication chains.
   */
  object SolveByElim extends ProofTactic with ProofSequentTactic {

    final case class Config(maxDepth: Int = 8)

    def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement =
      apply(Config())(bot)

    def apply(using lib: Library, proof: lib.Proof)(config: Config)(bot: F.Sequent): proof.ProofTacticJudgement = {
      if bot.right.size != 1 then
        return proof.InvalidProofTactic("`SolveByElim`: goal must have a single formula on the right-hand side.")

      val target = bot.right.head

      def stripForall(f: F.Expr[F.Prop]): (List[F.Variable[F.Ind]], F.Expr[F.Prop]) = f match
        case F.forall(x, body) =>
          val (xs, core) = stripForall(body)
          (x :: xs, core)
        case _ => (Nil, f)

      def stripImps(f: F.Expr[F.Prop]): (List[F.Expr[F.Prop]], F.Expr[F.Prop]) = f match
        case a ==> b =>
          val (ps, h) = stripImps(b)
          (a :: ps, h)
        case _ => (Nil, f)

      def computeInstantiation(clause: F.Expr[F.Prop], goal0: F.Expr[F.Prop]): Option[Map[F.Variable[F.Ind], F.Expr[F.Ind]]] = {
        val (xs, core) = stripForall(clause)
        val (_, head) = stripImps(core)
        val allowed: Set[F.Variable[?]] = xs.toSet.asInstanceOf[Set[F.Variable[?]]]
        val ctx = RewriteContext.withBound(head.freeVars.filterNot(allowed.contains))
        UnificationUtils.matchExpr(using ctx)(head, goal0).flatMap { subst =>
          xs.foldLeft(Option(Map.empty[F.Variable[F.Ind], F.Expr[F.Ind]])) { (acc, x) =>
            acc.flatMap(m => subst(x).map(t => m.updated(x, t)))
          }
        }
      }

      TacticSubproof {
        import lib.{have, lastStep}

        type GoalKey = (Set[lisa.utils.K.Expression], lisa.utils.K.Expression)

        def attempt(using p: lib.Proof)(j: p.ProofTacticJudgement, expected: F.Sequent): Option[p.Fact] =
          j match
            case v: p.ValidProofTactic @unchecked =>
              if F.isSameSequent(v.bot, expected) then Some(have(v))
              else None
            case _: p.InvalidProofTactic @unchecked => None

        def solve(using p: lib.Proof)(
            gamma: Set[F.Expr[F.Prop]],
            goal0: F.Expr[F.Prop],
            depth: Int,
            visited: Set[GoalKey]
        ): Option[p.Fact] = {
          if depth < 0 then return None

          val key: GoalKey = (gamma.map(_.underlying), goal0.underlying)
          if visited.contains(key) then return None
          val visited2 = visited + key

          val bot0: F.Sequent = gamma |- goal0

          if gamma.exists(F.isSame(_, goal0)) then
            return attempt(Hypothesis(using lib, p)(bot0), bot0)

          goal0 match
            case a /\ b =>
              val j = TacticSubproof(using p) {
                solve(using summon[lib.Proof])(gamma, a, depth - 1, visited2) match
                  case None => ()
                  case Some(fa) =>
                    solve(using summon[lib.Proof])(gamma, b, depth - 1, visited2) match
                      case None => ()
                      case Some(fb) =>
                        have(bot0) by RightAnd.withParameters(a, b)(fa, fb)
              }
              attempt(j, bot0)

            case a ==> b =>
              val j = TacticSubproof(using p) {
                solve(using summon[lib.Proof])(gamma + a, b, depth - 1, visited2) match
                  case None => ()
                  case Some(prem) =>
                    have(bot0) by RightImplies.withParameters(a, b)(prem)
              }
              attempt(j, bot0)

            case _ =>
              gamma.iterator
                .flatMap { clause =>
                  computeInstantiation(clause, goal0).iterator.flatMap { inst =>
                    val j = TacticSubproof(using p) {
                      useClause(using summon[lib.Proof])(gamma, goal0, clause, inst, depth - 1, visited2)
                    }
                    attempt(j, bot0).iterator
                  }
                }
                .toSeq
                .headOption
        }

        def useClause(using p: lib.Proof)(
            gamma: Set[F.Expr[F.Prop]],
            goal0: F.Expr[F.Prop],
            clause: F.Expr[F.Prop],
            inst: Map[F.Variable[F.Ind], F.Expr[F.Ind]],
            depth: Int,
            visited: Set[GoalKey]
        ): Unit = {
          val bot0: F.Sequent = gamma |- goal0
          if depth < 0 then return

          clause match
            case F.forall(x, phi) =>
              inst.get(x) match
                case None => ()
                case Some(t) =>
                  val instantiated = phi.substitute(x := t)
                  val gammaPrem = (gamma - clause) + instantiated
                  val prem = solve(using p)(gammaPrem, goal0, depth - 1, visited)
                  prem match
                    case None => ()
                    case Some(fprem) =>
                      have(bot0) by LeftForall.withParameters(phi, x, t)(fprem)

            case a ==> b =>
              (solve(using p)(gamma, a, depth - 1, visited), solve(using p)(gamma + b, goal0, depth - 1, visited)) match
                case (Some(fa), Some(fb)) =>
                  val prem1 = have(gamma |- (a, goal0)) by Weakening(fa)
                  have(bot0) by LeftImplies.withParameters(a, b)(prem1, fb)
                case _ => ()

            case _ =>
              if gamma.exists(F.isSame(_, goal0)) then
                have(bot0) by Hypothesis
              else ()
        }

        solve(bot.left, target, config.maxDepth, Set.empty) match
          case Some(f) =>
            have(bot) by Restate.from(f)
          case None =>
            return proof.InvalidProofTactic("`SolveByElim`: failed (depth limit reached or no applicable hypothesis).")
      }
    }
  }
}
