package lisa.automation.kernel

import lisa.automation.Tautology
import lisa.fol.FOLHelpers.*
import lisa.fol.FOL as F
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.{_, given}
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.prooflib.*
import lisa.utils.K

object CommonTactics {

  /**
   * <pre>
   * Γ |- ∃x. φ, Δ   Γ', φ, φ[y/x] |- x = y, Δ'
   * -------------------------------------------
   * Γ, Γ' |- ∃!x. φ, Δ, Δ'
   * </pre>
   *
   * This tactic separates the existence and the uniqueness proofs, which are often easier to prove independently, at
   * the expense of brevity.
   *
   * @see [[RightExistsOne]].
   */
  object ExistenceAndUniqueness extends ProofTactic {
    def withParameters(using lib: Library, proof: lib.Proof, om: OutputManager)(phi: F.Formula, x: F.Variable, y: F.Variable)(existence: proof.Fact, uniqueness: proof.Fact)(
        bot: F.Sequent
    ): proof.ProofTacticJudgement = {
      val existenceSeq = proof.getSequent(existence)
      val uniquenessSeq = proof.getSequent(uniqueness)

      lazy val substPhi = phi.substitute(x := y)
      lazy val existenceFormula = F.∃(x, phi)
      lazy val uniqueExistenceFormula = F.∃!(x, phi)

      // Checking that all formulas are present
      if (x == y) {
        proof.InvalidProofTactic("x and y can not be equal.")
      } else if (!F.contains(existenceSeq.right, existenceFormula)) {
        proof.InvalidProofTactic(s"Existence sequent conclusion does not contain ∃x. φ.")
      } else if (!F.contains(uniquenessSeq.left, phi)) {
        proof.InvalidProofTactic("Uniqueness sequent premises do not contain φ.")
      } else if (!F.contains(uniquenessSeq.left, substPhi)) {
        proof.InvalidProofTactic(s"Uniqueness sequent premises do not contain φ[y/x].")
      } else if (!F.contains(uniquenessSeq.right, x === y) && !F.contains(uniquenessSeq.right, y === x)) {
        proof.InvalidProofTactic(s"Uniqueness sequent conclusion does not contain x = y")
      } else if (!F.contains(bot.right, uniqueExistenceFormula)) {
        proof.InvalidProofTactic(s"Bottom sequent conclusion does not contain ∃!x. φ")
      }

      // Checking pivots
      else if (!F.isSameSet(existenceSeq.left ++ uniquenessSeq.left, bot.left + phi + substPhi)) {
        proof.InvalidProofTactic("Could not infer correct left pivots.")
      } else if (!F.isSameSet(existenceSeq.right ++ uniquenessSeq.right + uniqueExistenceFormula, bot.right + existenceFormula + (x === y))) {
        proof.InvalidProofTactic("Could not infer correct right pivots.")
      } else {
        val gammaPrime = uniquenessSeq.left.filter(f => !F.isSame(f, phi) && !F.isSame(f, substPhi))

        TacticSubproof {
          val x = variable
          val y = variable
          // There's got to be a better way of importing have/thenHave/assume methods
          // but I did not find one

          val forward = lib.have(phi |- ((x === y) ==> substPhi)) subproof {
            lib.assume(phi)
            lib.thenHave((x === y) |- substPhi) by RightSubstEq.withParametersSimple(List((x, y)), F.lambda(x, phi))
            lib.thenHave((x === y) ==> substPhi) by Restate
          }

          for (f <- gammaPrime) {
            lib.assume(f)
          }

          val backward = lib.have(phi |- (substPhi ==> (x === y))) by Restate.from(uniqueness)

          lib.have(phi |- ((x === y) <=> substPhi)) by RightIff(forward, backward)
          lib.thenHave(phi |- F.∀(y, (x === y) <=> substPhi)) by RightForall
          lib.thenHave(phi |- F.∃(x, F.∀(y, (x === y) <=> substPhi))) by RightExists
          lib.thenHave(F.∃(x, phi) |- F.∃(x, F.∀(y, (x === y) <=> substPhi))) by LeftExists
          lib.thenHave(F.∃(x, phi) |- F.∃!(x, phi)) by RightExistsOne

          lib.have(bot) by Cut(existence, lib.lastStep)
        }
      }
    }

    def apply(using lib: Library, proof: lib.Proof, om: OutputManager)(phi: F.Formula)(existence: proof.Fact, uniqueness: proof.Fact)(bot: F.Sequent): proof.ProofTacticJudgement = {
      val existenceSeq = proof.getSequent(existence)
      val uniquenessSeq = proof.getSequent(uniqueness)

      // Try to infer x from the premises
      // Specifically, find variables in the correct quantifiers, common to all three sequents
      val existsVars: Set[F.Variable] = existenceSeq.right.collect {
        case F.BinderFormula(F.Exists, x, f) if F.isSame(f, phi) => x
      }
      if (existsVars.isEmpty) {
        return proof.InvalidProofTactic("Missing existential quantifier in the existence sequent.")
      }

      val commonVars = bot.right.collect {
        case F.BinderFormula(F.ExistsOne, x, f) if F.isSame(f, phi) && existsVars.contains(x) => x
      }
      if (commonVars.size != 1) {
        return proof.InvalidProofTactic("Could not infer correct variable x in quantifiers.")
      }

      val x = commonVars.head

      // Infer y from the equalities in the uniqueness sequent
      uniquenessSeq.right.collectFirst {
        case F.AppliedPredicate(F.`equality`, Seq(`x`, (y: F.Variable))) if x != y && F.contains(uniquenessSeq.left, phi.substitute(x := y)) =>
          y

        case F.AppliedPredicate(F.`equality`, List(F.AppliedFunctional(y: F.Variable, _), F.AppliedFunctional(`x`, _))) if x != y && F.contains(uniquenessSeq.left, phi.substitute(x := y)) =>
          y
      } match {
        case Some(y) => ExistenceAndUniqueness.withParameters(phi, x, y)(existence, uniqueness)(bot)
        case None => proof.InvalidProofTactic("Could not infer correct variable y in uniqueness sequent.")
      }
    }
  }

  /**
   * <pre>
   *
   * -------------  if f(xs) = The(y, P(y)) is a function definition
   * |- P(f(xs))
   * </pre>
   * Here `xs` is an arbitrary list of parameters.
   *
   * If `f(xs) = The(y, (φ ==> Q(y)) /\ (!φ ==> (y === t)))` is a conditional function definition, then:
   * <pre>
   *
   * --------------
   * φ |- Q(f(xs))
   * </pre>
   */
  object Definition extends ProofTactic {
    def apply(using lib: Library, proof: lib.Proof)(f: F.ConstantFunctionLabel[?], uniqueness: proof.Fact)(xs: F.Term*)(bot: F.Sequent): proof.ProofTacticJudgement = {
      val expr = lib.getDefinition(f) match {
        case Some(value: lib.FunctionDefinition[?]) => value
        case _ => return proof.InvalidProofTactic("Could not get definition of function.")
      }
      val method: (F.ConstantFunctionLabel[?], proof.Fact) => Seq[F.Term] => F.Sequent => proof.ProofTacticJudgement =
        expr.f.substituteUnsafe(expr.vars.zip(xs).toMap) match {
          case F.AppliedConnector(
                F.And,
                Seq(
                  F.AppliedConnector(F.Implies, Seq(a, _)),
                  F.AppliedConnector(F.Implies, Seq(b, _))
                )
              ) if F.isSame(F.Neg(a), b) =>
            conditional(using lib, proof)

          case _ => unconditional(using lib, proof)
        }
      method(f, uniqueness)(xs)(bot)
    }

    /**
     * <pre>
     *
     * -------------  if f(xs) = The(y, P(y)) is a function definition
     * |- P(f(xs))
     * </pre>
     */
    def unconditional(using lib: Library, proof: lib.Proof)(f: F.ConstantFunctionLabel[?], uniqueness: proof.Fact)(xs: F.Term*)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lib.getDefinition(f) match {
        case Some(definition: lib.FunctionDefinition[?]) =>
          if (bot.right.size != 1) {
            return proof.InvalidProofTactic("Right-hand side of bottom sequent should contain only 1 formula.")
          }
          val y = definition.out
          val vars = definition.vars
          val fxs = f.applyUnsafe(xs)

          // Instantiate terms in the definition
          val subst = vars.zip(xs).map(tup => tup._1 := tup._2)
          val P = definition.f.substitute(subst*)
          val expected = P.substitute(y := fxs)
          if (!F.isSame(expected, bot.right.head)) {
            return proof.InvalidProofTactic("Right-hand side of bottom sequent should be of the form P(f(xs)).")
          }

          TacticSubproof {
            lib.have(F.∀(y, (y === fxs) <=> P)) by Tautology.from(uniqueness, definition.of(subst*))
            lib.thenHave((y === fxs) <=> P) by InstantiateForall(y)
            lib.thenHave((fxs === fxs) <=> P.substitute(y := fxs)) by InstFunSchema(Map(y -> fxs))
            lib.thenHave(P.substitute(y := fxs)) by Restate
          }

        case _ => proof.InvalidProofTactic("Could not get definition of function.")
      }
    }

    /**
     * <pre>
     *
     * -------------- if f(xs) = The(y, (φ ==> Q(y)) /\ (!φ ==> R(y)))
     * φ |- Q(f(xs))
     * </pre>
     */
    def conditional(using lib: Library, proof: lib.Proof)(f: F.ConstantFunctionLabel[?], uniqueness: proof.Fact)(xs: F.Term*)(bot: F.Sequent): proof.ProofTacticJudgement = {
      lib.getDefinition(f) match {
        case Some(definition: lib.FunctionDefinition[?]) =>
          if (bot.right.size != 1) {
            return proof.InvalidProofTactic("Right-hand side of bottom sequent should contain exactly 1 formula.")
          } else if (bot.left.isEmpty) {
            return proof.InvalidProofTactic("Left-hand side of bottom sequent should not be empty.")
          }
          val y = definition.out
          val vars = definition.vars

          // Extract variable labels to instantiate them later in the proof
          // val F.LambdaTermFormula(vars, _) = expr
          // val instantiations: Seq[(F.SchematicTermLabel, F.LambdaTermTerm)] = vars.zip(xs.map(x => F.LambdaTermTerm(Seq(), x)))

          val subst = vars.zip(xs).map(tup => tup._1 := tup._2)
          val P = definition.f.substitute(subst*)
          // Instantiate terms in the definition
          // val P = F.LambdaTermFormula(Seq(y), expr(xs))

          // Unfold the conditional definition to find Q
          val phi = F.And(bot.left.toSeq)
          val Q: F.LambdaExpression[F.Term, F.Formula, 1] = P.body match {
            case F.AppliedConnector(
                  F.And,
                  Seq(
                    F.AppliedConnector(F.Implies, Seq(a, f)),
                    F.AppliedConnector(F.Implies, Seq(b, g))
                  )
                ) if F.isSame(F.Neg(a), b) =>
              if (F.isSame(a, phi)) F.lambda(y, f)
              else if (F.isSame(b, phi)) F.lambda(y, g)
              else return proof.InvalidProofTactic("Condition of definition is not satisfied.")

            case _ =>
              return proof.InvalidProofTactic("Definition is not conditional.")
          }

          val fxs = f.applyUnsafe(xs)

          val expected = P.substitute(y := fxs)
          if (!F.isSame(expected, bot.right.head)) {
            return proof.InvalidProofTactic("Right-hand side of bottom sequent should be of the form Q(fxs).")
          }

          TacticSubproof {
            lib.have(F.∀(y, (y === fxs) <=> P)) by Tautology.from(uniqueness, definition.of(subst*))
            lib.thenHave((y === fxs) <=> P) by InstantiateForall(y)
            lib.thenHave((fxs === fxs) <=> P.substitute(y := fxs)) by InstFunSchema(Map(y -> fxs))
            lib.thenHave(P.substitute(y := fxs)) by Restate
            lib.thenHave(phi ==> Q(fxs)) by Tautology
            lib.thenHave(phi |- Q(fxs)) by Restate
          }

        case _ => proof.InvalidProofTactic("Could not get definition of function.")
      }
    }
  }

}
