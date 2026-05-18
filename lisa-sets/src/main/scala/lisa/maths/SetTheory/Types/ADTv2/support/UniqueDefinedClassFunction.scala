package lisa.maths.SetTheory.Types.ADTv2.support

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.Quantifiers.{existsOneEpsilon, existsOneEpsilonUniqueness}
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.BasicStepTactic.RightForall

final class UniqueDefinedClassFunction(
    name: String,
    typeVariablesSeq: Seq[Variable[Ind]],
    witnessVar: Variable[Ind],
    definitionAt: Expr[Ind] => Expr[Prop]
)(
    uniqueness: THM
) {

  private val witnessDefinition: Expr[Prop] = definitionAt(witnessVar)

  private val classFunction: Constant[?] = {
    val classFunctionExpr: Expr[?] = lisa.utils.fol.FOL.Abs.apply(
      xs = typeVariablesSeq,
      t = ε(witnessVar, witnessDefinition)
    )
    type S
    given lisa.utils.fol.FOL.IsSort[S] =
      lisa.utils.fol.FOL.unsafeSortEvidence(classFunctionExpr.sort)
    DEF(using name = name)(classFunctionExpr.asInstanceOf[Expr[S]])
  }
  classFunction.printAs(args => renderAppliedSymbol(name, typeVariablesSeq.size, args))

  val id: Identifier = classFunction.id

  def term(args: Seq[Expr[Ind]]): Expr[Ind] = (classFunction #@@ args).asInstanceOf[Expr[Ind]]

  val term: Expr[Ind] = term(typeVariablesSeq)

  private val classTermIsEpsilon: THM = Lemma(term === ε(witnessVar, witnessDefinition)) {
    have(thesis) by Congruence.from(classFunction.definition)
  }

  val definitionFact: THM = Lemma(definitionAt(term)) {
    val epsilonWitness = ε(witnessVar, witnessDefinition)

    val definitionAtEpsilon = have(definitionAt(epsilonWitness)) by Tautology.from(
      uniqueness,
      existsOneEpsilon of (x := witnessVar, P := λ(witnessVar, witnessDefinition))
    )
    val epsilonEqTerm = have(epsilonWitness === term) by Congruence.from(classTermIsEpsilon)

    val definitionAtEpsilonWithEq =
      have((epsilonWitness === term) |- definitionAt(epsilonWitness)) by
        Weakening(definitionAtEpsilon)

    val replacementVar = variable[Ind]
    val definitionAtTerm =
      have((epsilonWitness === term) |- definitionAt(term)) by
        RightSubstEq.withParameters(
          List((epsilonWitness, term)),
          (Seq(replacementVar), definitionAt(replacementVar))
        )(definitionAtEpsilonWithEq)

    have(thesis) by Tautology.from(epsilonEqTerm, definitionAtTerm)
  }

  val characterization: THM =
    Lemma(forall(witnessVar, (term === witnessVar) <=> witnessDefinition)) {
      val epsilonWitness = ε(witnessVar, witnessDefinition)

      val epsilonCharacterization = have(
        witnessDefinition <=> (witnessVar === epsilonWitness)
      ) by Tautology.from(
        uniqueness,
        existsOneEpsilonUniqueness of (
          x := witnessVar,
          y := witnessVar,
          P := λ(witnessVar, witnessDefinition)
        )
      )

      val classTermIsEps = have(term === epsilonWitness) by
        Congruence.from(classFunction.definition)

      val toRight = have((term === witnessVar) ==> (witnessVar === epsilonWitness)) subproof {
        assume(term === witnessVar)
        val termEqWitness = have(term === witnessVar) by Hypothesis
        val termEqEpsilon = have(term === epsilonWitness) by Tautology.from(classTermIsEps)
        have(witnessVar === epsilonWitness) by Congruence.from(termEqWitness, termEqEpsilon)
        thenHave(thesis) by Restate
      }

      val toLeft = have((witnessVar === epsilonWitness) ==> (term === witnessVar)) subproof {
        assume(witnessVar === epsilonWitness)
        val witnessEqEpsilon = have(witnessVar === epsilonWitness) by Hypothesis
        val termEqEpsilon = have(term === epsilonWitness) by Tautology.from(classTermIsEps)
        have(term === witnessVar) by Congruence.from(termEqEpsilon, witnessEqEpsilon)
        thenHave(thesis) by Restate
      }

      val equalityRewriting = have((term === witnessVar) <=> (witnessVar === epsilonWitness)) by
        Tautology.from(toRight, toLeft)

      have((term === witnessVar) <=> witnessDefinition) by
        Tautology.from(equalityRewriting, epsilonCharacterization)

      thenHave(thesis) by RightForall
    }
}
