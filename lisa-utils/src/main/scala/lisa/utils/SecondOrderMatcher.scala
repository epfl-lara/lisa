package lisa.utils

import lisa.kernel.fol.FOL.*

// TODO: connectors?

object SecondOrderMatcher {
  case class Matching(predicates: Map[SchematicPredicateLabel, LambdaTermTerm], functions: Map[SchematicFunctionLabel, LambdaTermFormula])

  private case class Renaming()

//  def findMatching(patterns: Seq[Formula], target: Seq[Formula]): Option[Matching] = {}

  // TODO: error reporting?
  private def isCorrectInput(patterns: Seq[Formula], target: Seq[Formula]): Boolean = ???

}
