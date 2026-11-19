package lisa.hol

import lisa.SetTheoryLibrary._
import lisa.hol.VarsAndFunctions._
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

class TypingCacheKeySuite extends AnyFunSuite:
  private object Owner extends lisa.HOL:
    val theorem = Theorem(⊤):
      have(thesis) by Restate

  private def typedOccurrences(term: Expr[?]): Vector[K.Identifier] = term match
    case variable: TypedVariable => Vector(variable.id)
    case App(function, argument) => typedOccurrences(function) ++ typedOccurrences(argument)
    case Abs(variable, body) => typedOccurrences(variable) ++ typedOccurrences(body)
    case _ => Vector.empty

  private def occurrences(proof: BaseProof)(term: Expr[Ind]): Vector[K.Identifier] =
    given proof.type = proof
    val typing = HOLSteps.HOLProofType(term)
    assert(K.SCProofChecker.checkSCProof(proof.toSCProof).isValid)
    assert(proof.justifications.forall(justification => !justification.withSorry))
    assert(typing.bot.left.isEmpty)
    typedOccurrences(typing.bot.right.collectFirst { case TypeAssign(value, _) => value }.get)

  test("keep annotation positions distinct within one root proof and across independent roots"):
    val typ = TypeVariable(K.Identifier("position-type"))
    val xId = K.Identifier("position-x")
    val yId = K.Identifier("position-y")
    val x = Variable[Ind](xId)
    val y = Variable[Ind](yId)
    val pair = Variable[Ind >>: Ind >>: Ind](K.Identifier("position-pair"))
    val first = pair(TypedVariable(xId, typ))(y)
    val second = pair(x)(TypedVariable(yId, typ))
    assert(first == second)
    for terms <- Seq(Seq(first -> xId, second -> yId), Seq(second -> yId, first -> xId)) do
      val proof = new BaseProof(Owner.theorem.asInstanceOf[THMFromProof])
      for (term, expected) <- terms do assert(occurrences(proof)(term) == Vector(expected))
      val size = proof.cachedRootStepCount
      for (term, expected) <- terms do assert(occurrences(proof)(term) == Vector(expected))
      assert(proof.cachedRootStepCount == size)
