package lisa.utils.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof as K
import lisa.kernel.proof.Sequent
import org.scalatest.funsuite.AnyFunSuite

class LinearProofSuite extends AnyFunSuite:
  private val p = Constant(Identifier("p"), Prop)
  private val statement = Sequent(Set(p), Set(p))

  test("empty proofs are rejected"):
    assert(LinearProof(Array.empty, Array.empty).check == Left(EmptyProofError))
 
  test("negative premises resolve to imported assumptions"):
    val result = LinearProof(Array(Restate(statement, -1)), Array(statement)).check

    assert(result.exists(_.assumptions == Set(statement)), "Expected the imported assumption to be used in the proof. Found result: " + result)

  test("invalid references are rejected before kernel dispatch"):
    assert(LinearProof(Array(Restate(statement, 0)), Array.empty).check == Left(ForwardReferenceError(0)))
    assert(LinearProof(Array(Restate(statement, -1)), Array.empty).check == Left(InvalidImportError(-1)))

  test("kernel errors retain step index"):
    val invalid = Sequent(Set.empty, Set(p))
    val result = LinearProof(Array(Hypothesis(invalid, p), Sorry(statement)), Array.empty).check

    result match
      case Left(InvalidStepError(0, _: K.Hypothesis.MissingFromLeft)) => succeed
      case other => fail(s"Unexpected result: $other")

  test("definition delegates to kernel and preserves its rule"):
    val c = Constant(Identifier("c"), Prop)
    val definition = Sequent(Set.empty, Set(iff(c)(top)))
    val result = LinearProof(Array(Definition(definition, c, Seq.empty, top)), Array.empty).check

    assert(result.exists(_.rule == K.Definition))
