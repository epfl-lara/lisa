package lisa.automation.kernel

import lisa.kernel.fol.FOL
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.{_, given}
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.prooflib.*
import lisa.utils.KernelHelpers.{_, given}
import lisa.automation.kernel.OLPropositionalSolver.Tautology

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
  def withParameters(using lib: Library, proof: lib.Proof, om: OutputManager)(phi: FOL.Formula, x: FOL.VariableLabel, y: FOL.VariableLabel)
                    (existence: proof.Fact, uniqueness: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
    val existenceSeq = proof.getSequent(existence)
    val uniquenessSeq = proof.getSequent(uniqueness)

    lazy val substPhi = substituteVariables(phi, Map[FOL.VariableLabel, FOL.Term](x -> y))
    lazy val existenceFormula = ∃(x, phi)
    lazy val uniqueExistenceFormula = ∃!(x, phi)

    // Checking that all formulas are present
    if (x == y) {
      proof.InvalidProofTactic("x and y can not be equal.")
    } else if (!contains(existenceSeq.right, existenceFormula)) {
      proof.InvalidProofTactic(s"Existence sequent conclusion does not contain ∃x. φ.")
    } else if (!contains(uniquenessSeq.left, phi)) {
      proof.InvalidProofTactic("Uniqueness sequent premises do not contain φ.")
    } else if (!contains(uniquenessSeq.left, substPhi)) {
      proof.InvalidProofTactic(s"Uniqueness sequent premises do not contain φ[y/x].")
    } else if (!contains(uniquenessSeq.right, x === y) && !contains(uniquenessSeq.right, y === x)) {
      proof.InvalidProofTactic(s"Uniqueness sequent conclusion does not contain x = y")
    } else if (!contains(bot.right, uniqueExistenceFormula)) {
      proof.InvalidProofTactic(s"Bottom sequent conclusion does not contain ∃!x. φ")
    }

    // Checking pivots
    else if (!isSameSet(existenceSeq.left ++ uniquenessSeq.left, bot.left + phi + substPhi)) {
      proof.InvalidProofTactic("Could not infer correct left pivots.")
    } else if (!isSameSet(existenceSeq.right ++ uniquenessSeq.right + uniqueExistenceFormula, bot.right + existenceFormula + (x === y))) {
      proof.InvalidProofTactic("Could not infer correct right pivots.")
    } else {
      val gammaPrime = uniquenessSeq.left.filter(f => !isSame(f, phi) && !isSame(f, substPhi))

      TacticSubproof {
        // There's got to be a better way of importing have/thenHave/assume methods
        // but I did not find one

        val forward = lib.have(phi |- ((x === y) ==> substPhi)) subproof {
          lib.assume(phi)
          lib.thenHave((x === y) |- substPhi) by RightSubstEq(List((x, y)), lambda(x, phi))
          lib.thenHave((x === y) ==> substPhi) by Restate
        }

        for (f <- gammaPrime) {
          lib.assume(f)
        }

        val backward = lib.have(phi |- (substPhi ==> (x === y))) by Restate.from(uniqueness)

        lib.have(phi |- ((x === y) <=> substPhi)) by RightIff(forward, backward)
        lib.thenHave(phi |- ∀(y, (x === y) <=> substPhi)) by RightForall
        lib.thenHave(phi |- ∃(x, ∀(y, (x === y) <=> substPhi))) by RightExists
        lib.thenHave(∃(x, phi) |- ∃(x, ∀(y, (x === y) <=> substPhi))) by LeftExists
        lib.thenHave(∃(x, phi) |- ∃!(x, phi)) by RightExistsOne

        lib.have(bot) by Cut(existence, lib.lastStep)
      }
    }
  }

  def apply(using lib: Library, proof: lib.Proof, om: OutputManager)(phi: FOL.Formula)(existence: proof.Fact, uniqueness: proof.Fact)
            (bot: Sequent): proof.ProofTacticJudgement = {
    val existenceSeq = proof.getSequent(existence)
    val uniquenessSeq = proof.getSequent(uniqueness)

    // Try to infer x from the premises
    // Specifically, find variables in the correct quantifiers, common to all three sequents
    val existsVars = existenceSeq.right.collect {
      case FOL.BinderFormula(FOL.Exists, x, f) if isSame(f, phi) => x
    }
    if (existsVars.isEmpty) {
      return proof.InvalidProofTactic("Missing existential quantifier in the existence sequent.")
    }

    val commonVars = bot.right.collect {
      case FOL.BinderFormula(FOL.ExistsOne, x, f) if isSame(f, phi) && existsVars.contains(x) => x
    }
    if (commonVars.size != 1) {
      return proof.InvalidProofTactic("Could not infer correct variable x in quantifiers.")
    }

    val x = commonVars.head

    // Infer y from the equalities in the uniqueness sequent
    uniquenessSeq.right.collectFirst {
      case FOL.PredicateFormula(FOL.`equality`, List(FOL.Term(`x`, _), FOL.Term(y: FOL.VariableLabel, _)))
        if x != y && contains(uniquenessSeq.left, substituteVariables(phi, Map[FOL.VariableLabel, FOL.Term](x -> y))) => y

      case FOL.PredicateFormula(FOL.`equality`, List(FOL.Term(y: FOL.VariableLabel, _), FOL.Term(`x`, _)))
        if x != y && contains(uniquenessSeq.left, substituteVariables(phi, Map[FOL.VariableLabel, FOL.Term](x -> y))) => y
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
  def apply(using lib: Library, proof: lib.Proof)
            (f: FOL.ConstantFunctionLabel, uniqueness: proof.Fact)(xs: FOL.Term*)
            (bot: Sequent): proof.ProofTacticJudgement = {
    lib.theory.getDefinition(f) match {
      case Some(lib.theory.FunctionDefinition(_, _, expr, _)) =>
        // Check if the definition is conditional
        val method = expr(xs) match {
          case FOL.ConnectorFormula(FOL.And, Seq(
            FOL.ConnectorFormula(FOL.Implies, Seq(a, _)),
            FOL.ConnectorFormula(FOL.Implies, Seq(b, _))
          )) if isSame(FOL.Neg(a), b) => conditional

          case _ => unconditional
        }

        method(f, uniqueness)(xs)(bot)

      case _ => proof.InvalidProofTactic("Could not get definition of function.")
    }
  }

  /**
   * <pre>
   *
   * -------------  if f(xs) = The(y, P(y)) is a function definition
   * |- P(f(xs))
   * </pre>
   */
  def unconditional(using lib: Library, proof: lib.Proof)
                    (f: FOL.ConstantFunctionLabel, uniqueness: proof.Fact)(xs: FOL.Term*)
                    (bot: Sequent): proof.ProofTacticJudgement = {
    lib.theory.getDefinition(f) match {
      case Some(definition @ lib.theory.FunctionDefinition(_, y, expr, _)) =>
        if (bot.right.size != 1) {
          return proof.InvalidProofTactic("Right-hand side of bottom sequent should contain only 1 formula.")
        }

        // Extract variable labels to instantiate them later in the proof
        val FOL.LambdaTermFormula(vars, _) = expr
        val instantiations: Seq[(FOL.SchematicTermLabel, FOL.LambdaTermTerm)] = vars.zip(xs.map(x => FOL.LambdaTermTerm(Seq(), x)))

        // Instantiate terms in the definition
        val P = FOL.LambdaTermFormula(Seq(y), expr(xs))

        val expected = P(Seq(f(xs)))
        if (!isSame(expected, bot.right.head)) {
          return proof.InvalidProofTactic("Right-hand side of bottom sequent should be of the form P(f(xs)).")
        }

        TacticSubproof {
          lib.have(∀(y, (y === f(xs)) <=> P(Seq(y)))) by Tautology.from(uniqueness, definition.of(instantiations: _*))
          lib.thenHave((y === f(xs)) <=> P(Seq(y))) by InstantiateForall(y)
          lib.thenHave((f(xs) === f(xs)) <=> P(Seq(f(xs)))) by InstFunSchema(Map(y -> f(xs)))
          lib.thenHave(P(Seq(f(xs)))) by Restate
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
  def conditional(using lib: Library, proof: lib.Proof)
                  (f: FOL.ConstantFunctionLabel, uniqueness: proof.Fact)(xs: FOL.Term*)
                  (bot: Sequent): proof.ProofTacticJudgement = {
    lib.theory.getDefinition(f) match {
      case Some(definition@lib.theory.FunctionDefinition(_, y, expr, _)) =>
        if (bot.right.size != 1) {
          return proof.InvalidProofTactic("Right-hand side of bottom sequent should contain exactly 1 formula.")
        } else if (bot.left.isEmpty) {
          return proof.InvalidProofTactic("Left-hand side of bottom sequent should not be empty.")
        }

        // Extract variable labels to instantiate them later in the proof
        val FOL.LambdaTermFormula(vars, _) = expr
        val instantiations: Seq[(FOL.SchematicTermLabel, FOL.LambdaTermTerm)] = vars.zip(xs.map(x => FOL.LambdaTermTerm(Seq(), x)))

        // Instantiate terms in the definition
        val P = FOL.LambdaTermFormula(Seq(y), expr(xs))

        // Unfold the conditional definition to find Q
        val phi = FOL.ConnectorFormula(FOL.And, bot.left.toSeq)
        val Q = P.body match {
          case FOL.ConnectorFormula(FOL.And, Seq(
            FOL.ConnectorFormula(FOL.Implies, Seq(a, f)),
            FOL.ConnectorFormula(FOL.Implies, Seq(b, g))
          )) if isSame(FOL.Neg(a), b) =>
            if (isSame(a, phi)) FOL.LambdaTermFormula(Seq(y), f)
            else if (isSame(b, phi)) FOL.LambdaTermFormula(Seq(y), g)
            else return proof.InvalidProofTactic("Condition of definition is not satisfied.")

          case _ => return proof.InvalidProofTactic("Definition is not conditional.")
        }

        val expected = Q(Seq(f(xs)))
        if (!isSame(expected, bot.right.head)) {
          return proof.InvalidProofTactic("Right-hand side of bottom sequent should be of the form Q(f(xs)).")
        }

        TacticSubproof {
          lib.have(∀(y, (y === f(xs)) <=> P(Seq(y)))) by Tautology.from(uniqueness, definition.of(instantiations: _*))
          lib.thenHave((y === f(xs)) <=> P(Seq(y))) by InstantiateForall(y)
          lib.thenHave((f(xs) === f(xs)) <=> P(Seq(f(xs)))) by InstFunSchema(Map(y -> f(xs)))
          lib.thenHave(P(Seq(f(xs)))) by Restate
          lib.thenHave(phi ==> Q(Seq(f(xs)))) by Tautology
          lib.thenHave(phi |- Q(Seq(f(xs)))) by Restate
        }

      case _ => proof.InvalidProofTactic("Could not get definition of function.")
    }
  }
}
