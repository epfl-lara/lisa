package lisa.utils.prooflib

import lisa.utils.K
import lisa.utils.fol.FOL.{_, given}
import org.scalatest.funsuite.AnyFunSuite

/**
 * Checks argument completion for functional definitions without changing their expressions.
 */
class FunctionalDefinitionSuite extends AnyFunSuite:
  private given library: Library = new Library
  private given OutputManager = new StringOutputManager
  import library.*

  private def assertDefinition(theorem: Thm, expected: Sequent): Unit =
    assert(K.isSameSequent(theorem.statement.underlying, expected.underlying))
    assert(theorem.kernel.assumptions.isEmpty && theorem.kernel.axioms.isEmpty && !theorem.usesSorry)

  test("DEF accepts functional aliases and aliases of aliases"):
    val x = variable[Ind]
    val identity = define("identity", lambda(x, x))._1
    val aliasFunction = DEF(identity)
    val aliasAgain = DEF(aliasFunction)
    for (alias, source) <- Seq((aliasFunction, identity), (aliasAgain, aliasFunction)) do
      val args = alias.definition.statement.right.head.freeVars.toSeq
      assert(args.size == 1 && args.head.sort == K.Ind)
      val arg = args.head.asInstanceOf[Variable[Ind]]
      assertDefinition(alias.definition, () |- (alias(arg) === source(arg)))

  test("remaining arguments are fresh with respect to explicit lambda parameters"):
    val x = Variable[Ind](K.Identifier("x", 40))
    val identity = define("partial-identity", lambda(x, x))._1
    val partialFunction = DEF(lambda(x, identity))
    val args = partialFunction.definition.statement.right.head.freeVars
    assert(args.size == 2 && args.contains(x))
    val extra = (args - x).head.asInstanceOf[Variable[Ind]]
    assert(extra.id != x.id)
    assertDefinition(partialFunction.definition, () |- (partialFunction(x)(extra) === identity(extra)))

  test("predicate aliases produce equivalences with arguments of the correct sorts"):
    val x = variable[Ind]
    val predicate = define("reflexive-predicate", lambda(x, x === x))._1
    val aliasPredicate = DEF(predicate)
    val arg = aliasPredicate.definition.statement.right.head.freeVars.head.asInstanceOf[Variable[Ind]]
    assertDefinition(aliasPredicate.definition, () |- (aliasPredicate(arg) <=> predicate(arg)))

  test("higher-order aliases complete every argument with its declared sort"):
    val f = variable[Ind >>: Ind]
    val x = variable[Ind]
    val applyFunction = define("apply-function", lambda(f, lambda(x, f(x))))._1
    val aliasHigherOrder = DEF(applyFunction)
    val args = aliasHigherOrder.definition.statement.right.head.freeVars
    assert(args.size == 2 && args.map(_.id).size == 2)
    val function = args.find(_.sort == f.sort).get.asInstanceOf[Variable[Ind >>: Ind]]
    val argument = args.find(_.sort == K.Ind).get.asInstanceOf[Variable[Ind]]
    assertDefinition(aliasHigherOrder.definition, () |- (aliasHigherOrder(function)(argument) === applyFunction(function)(argument)))

  test("argument completion does not permit free schematic variables in definitions"):
    val f = variable[Ind >>: Ind]
    val error = intercept[UserInvalidDefinitionException] { define("invalid-functional-alias", f) }
    assert(error.message.contains("ContainsSchematic"))
    assert(!defines(constant[Ind >>: Ind]("invalid-functional-alias")))
