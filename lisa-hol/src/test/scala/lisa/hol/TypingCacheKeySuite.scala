package lisa.hol

import lisa.SetTheoryLibrary
import lisa.hol.VarsAndFunctions.*
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.utils.K
import lisa.utils.fol.FOL.{*, given}
import lisa.utils.prooflib.*
import lisa.utils.prooflib.ProofHelpers.*
import org.scalatest.funsuite.AnyFunSuite

class TypingCacheKeySuite extends AnyFunSuite:
  private given Library = SetTheoryLibrary

  private def typedOccurrences(term: Expr[?]): Vector[K.Identifier] = term match
    case variable: TypedVariable => Vector(variable.id)
    case App(function, argument) => typedOccurrences(function) ++ typedOccurrences(argument)
    case Abs(variable, body) => typedOccurrences(variable) ++ typedOccurrences(body)
    case _ => Vector.empty

  private def occurrences(term: Expr[Ind]): Vector[K.Identifier] =
    val result = Subproof:
      have(HOLSteps.HOLProofType(term))
    assert(result.isValid)
    val theorem = result.thm
    assert(!theorem.kernel.usesSorry && theorem.statement.left.isEmpty)
    typedOccurrences(theorem.statement.right.collectFirst { case TypeAssign(value, _) => value }.get)

  test("keep annotation positions distinct when erased terms and annotation types coincide"):
    val typ = TypeVariable(K.Identifier("position-type"))
    val xId = K.Identifier("position-x")
    val yId = K.Identifier("position-y")
    val x = Variable[Ind](xId)
    val y = Variable[Ind](yId)
    val pair = Variable[Ind >>: Ind >>: Ind](K.Identifier("position-pair"))
    val first = pair(TypedVariable(xId, typ))(y)
    val second = pair(x)(TypedVariable(yId, typ))
    assert(first == second)
    try
      for terms <- Seq(Seq(first -> xId, second -> yId), Seq(second -> yId, first -> xId)) do
        HOLSteps.HOLProofType.resetCache()
        for (term, expected) <- terms do
          assert(occurrences(term) == Vector(expected))
        val size = HOLSteps.HOLProofType.cacheSize
        for (term, expected) <- terms do
          assert(occurrences(term) == Vector(expected))
        assert(HOLSteps.HOLProofType.cacheSize == size)
    finally HOLSteps.HOLProofType.resetCache()
