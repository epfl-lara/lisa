package lisa.test.utils

import lisa.kernel.fol.FOL._
import lisa.utils.KernelHelpers._
import lisa.utils.KernelHelpers.given_Conversion_Identifier_String
import lisa.utils.KernelHelpers.given_Conversion_String_Identifier
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.{_, given}

trait TestUtils {
  val (a, b, c) = (ConstantPredicateLabel("a", 0), ConstantPredicateLabel("b", 0), ConstantPredicateLabel("c", 0))
  val p = ConstantPredicateLabel("p", 1)
  val (x, y, z) = (VariableLabel("x"), VariableLabel("y"), VariableLabel("z"))
  val (x1, y1, z1) = (VariableLabel("x1"), VariableLabel("y1"), VariableLabel("z1"))
  val (xPrime, yPrime, zPrime) = (VariableLabel("x'"), VariableLabel("y'"), VariableLabel("z'"))
  val (cx, cy, cz) = (ConstantFunctionLabel("x", 0), ConstantFunctionLabel("y", 0), ConstantFunctionLabel("z", 0))
  val (f0, f1, f2, f3) = (ConstantFunctionLabel("f", 0), ConstantFunctionLabel("f", 1), ConstantFunctionLabel("f", 2), ConstantFunctionLabel("f", 3))
  val (sf1, sf2, sf3) = (SchematicFunctionLabel("f", 1), SchematicFunctionLabel("f", 2), SchematicFunctionLabel("f", 3))
  val (sPhi1, sPhi2) = (SchematicPredicateLabel("phi", 1), SchematicPredicateLabel("phi", 2))
  val (sc1, sc2) = (SchematicConnectorLabel("c", 1), SchematicConnectorLabel("c", 2))
  val (in, plus) = (ConstantPredicateLabel("elem", 2), ConstantFunctionLabel("+", 2))

  given Conversion[PredicateLabel, PredicateFormula] = PredicateFormula(_, Seq.empty)

  given Conversion[ConstantFunctionLabel, Term] = Term(_, Seq())

  given Conversion[VariableLabel, Term] = VariableTerm.apply
}
