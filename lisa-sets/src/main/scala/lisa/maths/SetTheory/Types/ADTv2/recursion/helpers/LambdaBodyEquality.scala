package lisa.maths.SetTheory.Types.ADTv2.recursion.helpers

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.tactics.Cuts
import lisa.utils.prooflib.BasicStepTactic.RightSubst

/**
 * Transports recursive-call equalities through branch bodies, including nested binders.
 */
private[recursion] object LambdaBodyEquality {

  /**
   * Proves body equality by simultaneous substitution of the available recursive-call equalities.
   */
  def prove(using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      assumptions: Set[Expr[Prop]],
      leftBody: Expr[Ind],
      rightBody: Expr[Ind],
      equalityFacts: Seq[proof.Fact]
  ): proof.Fact =
    if leftBody == rightBody then have(assumptions |- leftBody === rightBody) by RightRefl
    else if equalityFacts.nonEmpty then
      val equalities = equalityFacts
        .map { fact =>
          require(fact.statement.right.size == 1, "A recursive-call equality must have exactly one conclusion.")
          val formula = fact.statement.right.head
          asIndEquality(formula) match
            case Some(pair) => pair -> fact
            case None => throw IllegalArgumentException(s"Expected a recursive-call equality, got $formula.")
        }
        .distinctBy(_._1)
      val pairs = equalities.map(_._1)
      val reserved: Seq[Expr[?]] = Seq(leftBody, rightBody) ++ assumptions ++
        equalityFacts.flatMap(fact => fact.statement.left ++ fact.statement.right)
      val firstHole = freshId(reserved, "recursiveValue")
      val holes = pairs.indices.map(i => Variable[Ind](Identifier(firstHole.name, firstHole.no + i)))
      // Expr.rewrite abstracts exact call occurrences without capturing variables under binders.
      val template = pairs.zip(holes).foldLeft(leftBody) { case (body, ((left, _), hole)) =>
        body.rewrite(left, hole)
      }
      val equations = pairs.map((left, right) => left === right).toSet
      val refl = have(leftBody === leftBody) by RightRefl
      val transported = have((assumptions ++ equations) |- leftBody === rightBody) by
        RightSubst(pairs, holes -> (leftBody === template))(refl)
      have(assumptions |- leftBody === rightBody) by Cuts(transported)(equalities.map(_._2)*)
    else
      throw IllegalArgumentException(
        s"Cannot prove body equality without recursive equalities: $leftBody vs $rightBody."
      )

}
