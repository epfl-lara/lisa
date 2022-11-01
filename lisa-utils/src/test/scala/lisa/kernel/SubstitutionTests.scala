package lisa.kernel

import lisa.kernel.fol.FOL
import lisa.kernel.fol.FOL.*
import lisa.test.ProofCheckerSuite
import lisa.utils.Helpers.*
import lisa.utils.Helpers.*
import lisa.utils.Printer
import org.scalatest.funsuite.AnyFunSuite

import scala.language.implicitConversions

class SubstitutionTests extends ProofCheckerSuite {

  def constant_symbol(label: String, args: Seq[Term]): Term = {
    Term(ConstantFunctionLabel(label, args.length), args)
  }

  def schematic_symbol(label: String, args: Seq[Term]): Term = {
    Term(SchematicFunctionLabel(label, args.length), args)
  }

  // ####################ON TERMS####################
  test("Substituting on a single term") {
    val g = constant_symbol("g", Seq(x, y))
    val h = constant_symbol("h", Seq(g, z, w))
    val t = substituteVariables(
      h,
      Map(
        xl -> u,
        VariableLabel("b") -> y,
        wl -> v
      )
    ) // h(g(u, y), z, v)
    assert(isSame(t, Term(ConstantFunctionLabel("h", 3), Seq(Term(ConstantFunctionLabel("g", 2), Seq(u, y)), z, v))))
  }

  test("Substituting a function symbol with arity >= 0") {

    val f = constant_symbol("f", Seq(x, z))
    val g = schematic_symbol("g", Seq(xp, yp, zp))

    val t = instantiateTermSchemas(
      g,
      Map(
        xpl -> LambdaTermTerm(Nil, f),
        xl -> LambdaTermTerm(Nil, v),
        SchematicFunctionLabel("g", 3) -> LambdaTermTerm(Seq(ul, vl, wl), Term(ConstantFunctionLabel("g", 3), Seq(u, v, w)))
      )
    ) // \u, v, w. g(f(x, z), y', z')

    assert(isSame(t, constant_symbol("g", Seq(f, yp, zp))))
  }

  test("Substituting simultaneously terms that reference each others") {

    val f = constant_symbol("f", Seq(x))

    val t = instantiateTermSchemas(
      f,
      Map(
        xl -> LambdaTermTerm(Nil, y),
        yl -> LambdaTermTerm(Nil, z)
      )
    )

    assert(isSame(t, constant_symbol("f", Seq(y))))

  }

  test("Substituting simultaneously terms that reference each others (2)") {

    val f = constant_symbol("f", Seq(x, y))
    val g = schematic_symbol("g", Seq(f, x))
    val h = constant_symbol("h", Seq(g, z))
    val t = instantiateTermSchemas(
      h,
      Map(
        xl -> LambdaTermTerm(Nil, f),
        SchematicFunctionLabel("g", 2) -> LambdaTermTerm(Seq(ul, vl), Term(ConstantFunctionLabel("g", 2), Seq(u, v)))
      )
    )

    assert(isSame(t, constant_symbol("h", Seq(constant_symbol("g", Seq(constant_symbol("f", Seq(f, y)), f)), z))))
  }

  test("Multiple non modifying operations on a term") {
    val f = constant_symbol("f", Seq(x, y))
    val g = schematic_symbol("g", Seq(f, z))
    val h = constant_symbol("h", Seq(g, w))
    val t = instantiateTermSchemas(
      h,
      Map[SchematicTermLabel, LambdaTermTerm](
        vl -> LambdaTermTerm(Nil, u),
        SchematicFunctionLabel("g\u0000", 2) -> LambdaTermTerm(Seq(xl, yl), u),
        SchematicFunctionLabel("f", 2) -> LambdaTermTerm(Seq(xl, yl), u),
        SchematicFunctionLabel("g", 1) -> LambdaTermTerm(Seq(xl), u),
        SchematicFunctionLabel("test", 1) -> LambdaTermTerm(Seq(xl), u)
      )
    ) // h(g(f(x, y), w), w)

    assert(isSame(t, h))
  }

  test("Instantiating a term that blocks another ") {
    val f = constant_symbol("f", Seq(x, y))
    val g = schematic_symbol("g", Seq(f, z))
    val h = constant_symbol("h", Seq(g, w))
    val t = instantiateTermSchemas(
      h,
      Map[SchematicTermLabel, LambdaTermTerm](
        xl -> LambdaTermTerm(Nil, f),
        SchematicFunctionLabel("g", 2) -> LambdaTermTerm(Seq(xl, yl), v)
      )
    ) // h(v, w)
    assert(isSame(t, constant_symbol("h", Seq(v, w))))
  }

  test("Substituting variables in a formula") {

    val f = ConstantPredicateLabel("F", 1)
    val formula: Formula = (f(x) <=> f(y)) /\ (x === y) /\ BinderFormula(Forall, xl, f(x) ==> f(y))

    val form = substituteVariables(
      formula,
      Map[VariableLabel, Term](
        xl -> u,
        yl -> v
      )
    )

    assert(isSame(form, (f(u) <=> f(v)) /\ (u === v) /\ BinderFormula(Forall, xl, f(x) ==> f(v))))
  }

  test("Substituting variables in a formula (2)") {

    val f = ConstantPredicateLabel("F", 1)
    val formula: Formula = (f(x) <=> f(y)) /\ (x === y) /\ BinderFormula(Forall, xl, f(x) ==> f(y))
    val form = substituteVariables(
      formula,
      Map[VariableLabel, Term](
        xl -> u,
        ul -> x
      )
    )

    assert(isSame(form, (f(u) <=> f(y)) /\ (u === y) /\ BinderFormula(Forall, xl, f(x) ==> f(y))))
  }

  test("Substituting noon existing variables in a formula") {

    val f = ConstantPredicateLabel("F", 1)
    val formula: Formula = (f(x) <=> f(y)) /\ (x === y) /\ BinderFormula(Forall, xl, f(x) ==> f(y))

    val form = substituteVariables(
      formula,
      Map[VariableLabel, Term](
        zl -> u
      )
    )

    assert(isSame(form, formula))
  }

  test("Substituting VariableFormulaLabel with colliding names") {
    val b = VariableLabel("b")()
    val ap = VariableFormulaLabel("a")()
    val bp = VariableFormulaLabel("b")()
    val cp = VariableFormulaLabel("c")()
    val bpp = SchematicFunctionLabel("b", 1)
    val f = ConstantPredicateLabel("F", 1)
    val bc = ConstantPredicateLabel("b", 1)
    val bn = ConstantPredicateLabel("b", 0)
    val bppp = SchematicPredicateLabel("b", 0)
    val cppp = SchematicPredicateLabel("c", 0)
  
    val formula : Formula = (ap <=> bppp()) /\ BinderFormula(Forall, xl, BinderFormula(Forall,VariableLabel("b"), ap <=> bp) /\ (bc(bpp(b))))
  
    val form = substituteFormulaVariables(formula, Map(
        VariableFormulaLabel("a") -> bp,
        VariableFormulaLabel("b") -> cp))
  
    val form2 = substituteFormulaVariables(formula, Map(
        VariableFormulaLabel("a") -> bn(),
        VariableFormulaLabel("b") -> cp,
      ))
    assert(!isSame(form, form2))
  
  }
   
  test("Verifying predicates on instantiatePredicateSchemas") {
    val f = SchematicPredicateLabel("F", 1)

    val ap = VariableFormulaLabel("a")
    val bp = VariableFormulaLabel("b")
    val h = ( f(x) <=> ap())

    val t = instantiatePredicateSchemas(h, Map[SchematicVarOrPredLabel, LambdaTermFormula](

      f -> LambdaTermFormula(Seq(xl), ((x === x) <=> ap() )),
      ap -> LambdaTermFormula(Seq(), bp()),

    )) // h(f(a), g(b))
    assert(isSame(t, (( ((x === x)  <=> ap()) <=> bp()))))

  }
   

  test("Verifying instantiateConnectorSchemas on Connectors") {
    val f = ConstantPredicateLabel("F", 1)
    val g = ConstantPredicateLabel("G", 1)
    val h = SchematicConnectorLabel("conn", 2)

    val ap = VariableFormulaLabel("a")
    val bp = VariableFormulaLabel("b")

    val t = instantiateConnectorSchemas(
      h(f(x), g(y)),
      Map[SchematicConnectorLabel, LambdaFormulaFormula](
        h -> LambdaFormulaFormula(Seq(ap, bp), (ap() <=> bp()))
      )
    )
    assert(isSame(t, (f(x) <=> g(y))))
  }


 // FIXME: depends on printer error reported in issue 81
  /**
  test("Verifying instantiatePredicateSchemas & instantiateConnectorSchemas on Binders") {
    val f = SchematicPredicateLabel("F", 1)
    val g = ConstantPredicateLabel("G", 1)
    val h = SchematicConnectorLabel("conn", 2)

    val ap = VariableFormulaLabel("a")
    val bp = VariableFormulaLabel("b")

    val t = instantiatePredicateSchemas(exists(xl, h(f(x), forall(yl, g(y)))) , Map[SchematicVarOrPredLabel, LambdaTermFormula](

      f -> LambdaTermFormula(Seq(xl), ((x === x) <=> ap() )),
      ap -> LambdaTermFormula(Seq(), bp()),

    ))

    val t2 = instantiateConnectorSchemas(t, Map[SchematicConnectorLabel, LambdaFormulaFormula](
      h -> LambdaFormulaFormula(Seq(ap, bp), (ap()  <=> bp()))

    ))
    println(Printer.prettyFormula(t2))
    println(Printer.prettyFormula(t))

    assert(isSame(t2, (f(x) <=> g(y))))

  }**/
  
   

  // FIXME: likely depends on Printer error reported in issue 81
  /**
  test("Verifying instantiateTermSchemas") {
    val f = SchematicFunctionLabel("F", 1)
    val g = SchematicFunctionLabel("G", 1)
    val p = ConstantPredicateLabel("P", 2)
    val h = SchematicConnectorLabel("conn", 2)

    val ap = VariableFormulaLabel("a")
    val bp = VariableFormulaLabel("b")

    val t = instantiateTermSchemas(h(p(f(g(x)), g(y)) , (x === y)), Map[SchematicTermLabel, LambdaTermTerm](

      f -> LambdaTermTerm(Seq(xl), (g(x))),
      g -> LambdaTermTerm(Seq(xl), f(g(x))),
      xl -> LambdaTermTerm(Seq(), y),
      yl -> LambdaTermTerm(Seq(), f(x)),

    ))

    assert(isSame(t, h(p(g(f(g(y))), g(f(x))) , (y === f(x)))))
  }
   **/
}