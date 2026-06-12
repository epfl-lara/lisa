package lisa.maths.SetTheory.Types.ADTv2.support.semantics

import lisa.maths.Quantifiers.existsOneAlternativeDefinition
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.utils.prooflib.BasicStepTactic.RightForall

final class ExistsOneBuilder(
    witnessVar: Variable[Ind],
    definitionAt: Expr[Ind] => Expr[Prop],
    existence: THM,
    pairwiseUniqueness: THM
) {

  private val witnessDefinition = definitionAt(witnessVar)

  val theorem: THM = Lemma(existsOne(witnessVar, witnessDefinition)) {
    val definitionFormula = (v: Variable[Ind]) => definitionAt(v)

    val existencePart = have(∃(x, definitionFormula(x))) by
      Restate.from(existence of (witnessVar := x))

    have(definitionFormula(x) /\ definitionFormula(y) ==> (x === y)) by
      Restate.from(pairwiseUniqueness)
    thenHave(∀(y, definitionFormula(x) /\ definitionFormula(y) ==> (x === y))) by RightForall

    val uniquenessAll = thenHave(
      ∀(x, ∀(y, definitionFormula(x) /\ definitionFormula(y) ==> (x === y)))
    ) by RightForall

    have(
      ∃(x, definitionFormula(x)) /\
        ∀(x, ∀(y, definitionFormula(x) /\ definitionFormula(y) ==> (x === y)))
    ) by Tautology.from(existencePart, uniquenessAll)

    have(thesis) by Tautology.from(
      lastStep,
      existsOneAlternativeDefinition of (x := witnessVar, P := λ(witnessVar, witnessDefinition))
    )
  }
}
