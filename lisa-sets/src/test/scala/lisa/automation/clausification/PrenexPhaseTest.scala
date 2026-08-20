package lisa.automation.clausification

import lisa.kernel.KernelProof
import lisa.utils.K.{_, given}
import org.scalatest.funsuite.AnyFunSuite

/**
 * Prenex stripping on the shape that used to separate the two strategies: a `∀` whose sibling mentions the
 * binder's identifier free, as in `(∀z. Pc(z)) ∧ Qc(z)`.
 *
 * The removed rewrite strategy lifted the `∀` over that sibling with a library equivalence, which is a theorem
 * only because the closed side is a nullary schema, so it had to α-rename to avoid capturing the sibling's `z`,
 * and it got that wrong once. `provePrenex` never moves a quantifier, so the case is unremarkable here, and
 * that is what these tests pin: the sibling's free variable survives into the matrix.
 */
class PrenexPhaseTest extends AnyFunSuite:

  private val Pc = Constant(Identifier("Pc", 0), Ind >>: Prop)
  private val Qc = Constant(Identifier("Qc", 0), Ind >>: Prop)
  private val zv = Variable(Identifier("z", 0), Ind)
  private val yv = Variable(Identifier("y", 0), Ind)

  /**
   * Run `PrenexPhase`'s entry point on `phi` exactly as `certifyPrenex` does, and return the composed proof
   * together with the matrix it derived.
   */
  private def prenex(phi: Expression): (SCProof, Expression) =
    val ax = () |- phi
    val (sub, matrixAx) = PrenexPhase.provePrenex(ax, -1, Clausification.Counter())
    (SCProof(IndexedSeq(sub), IndexedSeq(ax) ++ Clausification.libImports), matrixAx.right.head)

  test("a ∀ whose sibling mentions the binder free is stripped without capturing it") {
    val fa = forall(zv, Application(Pc, zv))
    for (name, inner) <- List(
        ("AndL", and(fa)(Application(Qc, zv))),
        ("AndR", and(Application(Qc, zv))(fa)),
        ("OrL", or(fa)(Application(Qc, zv))),
        ("OrR", or(Application(Qc, zv))(fa))
      )
    do
      val phi = and(inner)(Application(Qc, yv))
      val (proof, matrix) = prenex(phi)
      KernelProof.assertCorrectProofNoSorry(proof, s"$name (capturing sibling)")
      assert(proof.conclusion == (() |- matrix), s"$name: unexpected conclusion ${proof.conclusion}")
      // The sibling's `z` is a different variable from the ∀'s bound `z` and must still be free in the matrix.
      assert(matrix.freeVariables.contains(zv), s"$name: the sibling's free variable was captured; matrix $matrix")
  }
