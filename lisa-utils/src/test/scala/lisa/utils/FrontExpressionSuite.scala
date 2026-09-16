package lisa.utils

import lisa.utils.fol.FOL.{*, given}
import org.scalatest.funsuite.AnyFunSuite

class FrontExpressionSuite extends AnyFunSuite:
  private final class TaggedConstant(id: Identifier) extends Constant[Ind](id)

  test("distinguish equal identifiers with different sorts"):
    val id = K.Identifier("same-name")
    val individual = Variable[Ind](id)
    val proposition = Variable[Prop](id)
    assert(individual != proposition)
    assert(Set[Expr[?]](individual, proposition).size == 2)
    assert(Constant[Ind](id) != Constant[Prop](id))
    assert(individual != Constant[Ind](id))

  test("share equality and hashing across typed frontend wrappers"):
    val id = K.Identifier("tagged")
    val plain = Constant[Ind](id)
    val tagged = new TaggedConstant(id)
    assert(plain == tagged && tagged == plain)
    assert(plain.hashCode == tagged.hashCode)
    assert(Set[Expr[Ind]](plain, tagged).size == 1)

  test("hash equal applications and abstractions identically"):
    val x = Variable[Ind](K.Identifier("x"))
    val otherX = Variable[Ind](K.Identifier("x"))
    val p = Constant[Ind >>: Prop](K.Identifier("P"))
    val first = λ(x, p(x))
    val second = λ(otherX, p(otherX))
    assert(first == second)
    assert(first.hashCode == second.hashCode)
    assert(first.hashCode == first.underlying.hashCode)

  test("avoid capturing an existing free variable when renaming a binder"):
    val x = Variable[Ind](K.Identifier("x"))
    val x1 = Variable[Ind](K.Identifier("x", 1))
    val y = Variable[Ind](K.Identifier("y"))
    val p = Constant[Ind >>: Ind >>: Prop](K.Identifier("P"))
    val original = λ(x, p(x1)(y))
    val result = original.substitute(y := x)
    assert(result.freeVars == Set(x, x1))
    val kernelResult = K.substituteVariables(original.underlying, Map(y.underlying -> x.underlying))
    assert(kernelResult.freeVariables == Set(x.underlying, x1.underlying))
    assert(result.underlying == kernelResult)

  test("copy expressions through their identity allocator"):
    val x = K.Variable(K.Identifier("copy-x"), K.Ind)
    val y = K.Variable(K.Identifier("copy-y"), K.Ind)
    val f = K.Constant(K.Identifier("copy-f"), K.Arrow(K.Ind, K.Ind))
    val original = K.Application(f, x)
    val copied = original.copy(arg = y)
    assert(copied != original)
    assert(copied.uniqueNumber != original.uniqueNumber)
    assert(copied == K.Application(f, y))
    assert(copied.hashCode == K.Application(f, y).hashCode)
    assert(x.copy().hashCode == x.hashCode)

  test("retain equality and hash-set membership across cache rotations"):
    val x = K.Variable(K.Identifier("rotation-x"), K.Ind)
    val f = K.Constant(K.Identifier("rotation-f"), K.Arrow(K.Ind, K.Ind))
    val original = K.Application(f, x)
    val abstraction = K.Lambda(x, original)
    val retained = Set[K.Expression](original, abstraction)
    // Run with -Dlisa.hashcons.max=8 to force several generations to expire.
    (0 until 256).foreach: i =>
      val argument = K.Variable(K.Identifier("rotation-fill", i), K.Ind)
      K.Lambda(argument, K.Application(f, argument))
    val rebuilt = K.Application(f, x)
    val rebuiltAbstraction = K.Lambda(x, rebuilt)
    assert(original == rebuilt && abstraction == rebuiltAbstraction)
    assert(retained.contains(rebuilt) && retained.contains(rebuiltAbstraction))
    val enabled = !sys.props.get("lisa.hashcons").exists(Set("false", "0")) &&
      !sys.env.get("LISA_HASHCONS").exists(Set("false", "0"))
    if enabled && sys.props.getOrElse("lisa.hashcons.mode", "hybrid") != "bounded" then
      assert(original.uniqueNumber == rebuilt.uniqueNumber)
      assert(abstraction.uniqueNumber == rebuiltAbstraction.uniqueNumber)
