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

    have(∀(y, definitionAt(x) /\ definitionAt(y) ==> (x === y))) by RightForall(pairwiseUniqueness)
    val uniquenessAll = thenHave(
      ∀(x, ∀(y, definitionAt(x) /\ definitionAt(y) ==> (x === y)))
    ) by RightForall

    have(thesis) by Tautology.from(
      existence of (witnessVar := x),
      uniquenessAll,
      existsOneAlternativeDefinition of (x := witnessVar, P := λ(witnessVar, witnessDefinition))
    )
  }
}
