package lisa.kernel

import lisa.kernel.fol.FOL
import lisa.kernel.fol.FOL.*
import lisa.utils.Helpers.*
import lisa.utils.Printer
import org.scalatest.funsuite.AnyFunSuite
import lisa.test.ProofCheckerSuite
import lisa.utils.Helpers.*

import scala.language.implicitConversions


class SubstitutionTests extends ProofCheckerSuite {
 
  def constant_symbol(label : String, args : Seq[Term]) : Term = {
    Term(ConstantFunctionLabel(label, args.length), args)
  }

  def schematic_symbol(label : String, args : Seq[Term]) : Term = {
    Term(SchematicFunctionLabel(label, args.length), args)
  }

  //####################ON TERMS####################
  test("Substituting on a single term") {
    val g = constant_symbol("g", Seq(x, y)) // \u, v. g(u, v), g(x,y)
    val h = constant_symbol("h", Seq(g, z, w)) // \u, v, t. h(u, v, t), h(g(x,y), z, t)
    val t = substituteVariables(h, Map(
      xl -> u, 
      VariableLabel("b") -> y,  
      wl -> v
    )) // h(g(u, y), z, v)
    assert(isSame(t, Term(ConstantFunctionLabel("h", 3), Seq(Term(ConstantFunctionLabel("g", 2), Seq(u, y)), z, v))))
  }

  test("Substituting a function symbol with arity >= 0") {
    
    val f = constant_symbol("f", Seq(x, z)) // \u, v. f(u, v), f(x, z)
    val g = schematic_symbol("g", Seq(xp, yp, zp)) // \u, v, w. ?g(x', y', z')
    
    val t = instantiateTermSchemas(g, Map(
      xpl -> LambdaTermTerm(Nil, f), 
      xl  -> LambdaTermTerm(Nil, v),
      SchematicFunctionLabel("g", 3)   -> LambdaTermTerm(Seq(ul,vl,wl), Term(ConstantFunctionLabel("g", 3), Seq(u, v, w)))
    )) // \u, v, w. g(f(x, z), y', z')

    assert(isSame(t, constant_symbol("g", Seq(f, yp, zp))))
  }

  test("Substituting simultaneously terms that reference each others") {

    val f = constant_symbol("f", Seq(x)) // \u. f(u), f(x)
    
    val t = instantiateTermSchemas(f, Map(
      xl  -> LambdaTermTerm(Nil, y),
      yl  -> LambdaTermTerm(Nil, z)
    )) 

    assert(isSame(t, constant_symbol("f", Seq(y))))

  }

  test("Substituting simultaneously terms that reference each others (2)") {

    val f = constant_symbol("f", Seq(x, y))  // \u, v. f(u, v), f(x, y)
    val g = schematic_symbol("g",Seq(f, x)) // \u, v. g(u, v), g(f(x, y), x)
    val h = constant_symbol("h", Seq(g, z)) // \u, v. h(u, v), h(g(f(x, y), x), z)
    val t = instantiateTermSchemas(h, Map(
      xl  -> LambdaTermTerm(Nil, f),
      SchematicFunctionLabel("g", 2) -> LambdaTermTerm(Seq(ul, vl), Term(ConstantFunctionLabel("g", 2), Seq(u, v)))
    )) 
    
    assert(isSame(t, constant_symbol("h", Seq(constant_symbol("g", Seq(constant_symbol("f", Seq(f, y)), f)), z))))
  }

  test("Multiple non modifying operations on a term") {
    val f = constant_symbol("f", Seq(x, y)) // \u, v. f(u, v), f(x, y)
    val g = schematic_symbol("g", Seq(f, z)) // \u, v. g(u, v), g(f(x, y), z)
    val h = constant_symbol("h", Seq(g, w)) // \u, v. h(u, v), h(g(f(x, y), z), w)
    val t = instantiateTermSchemas(h, Map[SchematicTermLabel, LambdaTermTerm](
      vl  -> LambdaTermTerm(Nil, u),
      SchematicFunctionLabel("f", 2) -> LambdaTermTerm(Seq(xl, yl), u),
      SchematicFunctionLabel("g", 1) -> LambdaTermTerm(Seq(xl), u),
      SchematicFunctionLabel("test", 1)  -> LambdaTermTerm(Seq(xl), u)
    )) // h(g(f(x, y), w), w)

    assert(isSame(t, h))
  }

  test("Instantiating a term that blocks another ") {
    val f = constant_symbol("f", Seq(x, y)) // \u, v. f(u, v), f(x, y)
    val g = schematic_symbol("g", Seq(f, z)) // \u, v. g(u, v), g(f(x, y), z)
    val h = constant_symbol("h", Seq(g, w)) // \u, v. h(u, v), h(g(f(x, y), z), w)
    val t = instantiateTermSchemas(h, Map[SchematicTermLabel, LambdaTermTerm](
      xl  -> LambdaTermTerm(Nil, f),
      SchematicFunctionLabel("g", 2)  -> LambdaTermTerm(Seq(xl, yl), v),
    )) // h(v, w)
    assert(isSame(t, constant_symbol("h", Seq(v, w))))
  }

  test("Substituting variables in a formula") {
  
    val f = ConstantPredicateLabel("F", 1)
    val formula : Formula = (f(x) <=> f(y)) /\ (x === y) /\ BinderFormula(Forall, xl, f(x) ==> f(y)) // F(x) <=> F(y) /\ x === y /\ \z. F(z) ==> F(y)

    val form = substituteVariables(formula, Map[VariableLabel, Term](
      xl -> u,
      yl -> v
    )) // F(u) <=> F(v) /\ u === v /\ \x. F(x) ==> F(v)

    assert(isSame(form, (f(u) <=> f(v)) /\ (u === v) /\ BinderFormula(Forall, xl, f(x) ==> f(v))))
  }

  test("Substituting variables in a formula (2)") {
  
    val f = ConstantPredicateLabel("F", 1)
    val formula : Formula = (f(x) <=> f(y)) /\ (x === y) /\ BinderFormula(Forall, xl, f(x) ==> f(y)) // F(x) <=> F(y) /\ x === y /\ \z. F(z) ==> F(y)

    val form = substituteVariables(formula, Map[VariableLabel, Term](
      xl -> u,
      ul -> x
    )) // F(u) <=> F(y) /\ u === y /\ \x. F(x) ==> F(y)

    assert(isSame(form, (f(u) <=> f(y)) /\ (u === y) /\ BinderFormula(Forall, xl, f(x) ==> f(y))))
  }

  test("Substituting noon existing variables in a formula") {
  
    val f = ConstantPredicateLabel("F", 1)
    val formula : Formula = (f(x) <=> f(y)) /\ (x === y) /\ BinderFormula(Forall, xl, f(x) ==> f(y)) // F(x) <=> F(y) /\ x === y /\ \z. F(z) ==> F(y)

    val form = substituteVariables(formula, Map[VariableLabel, Term](
      zl -> u
    )) // F(x) <=> F(y) /\ x === y /\ \z. F(z) ==> F(y)

    assert(isSame(form, formula))
  }

  //error ?
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

    val formula : Formula = (ap <=> bppp()) /\ BinderFormula(Forall, xl, BinderFormula(Forall,VariableLabel("b"), ap <=> bp) /\ (bc(bpp(b)))) // F(x) <=> F(y) /\ x === y /\ \z. F(z) ==> F(y)

    val form = substituteFormulaVariables(formula, Map(
      VariableFormulaLabel("a") -> bp,
      VariableFormulaLabel("b") -> cp,
    )) // F(u) <=> F(y) /\ u === y /\ \x. F(x) ==> F(y)

    val form2 = substituteFormulaVariables(formula, Map(
      VariableFormulaLabel("a") -> bn(),
      VariableFormulaLabel("b") -> cp,
    )) 

    println(Printer.prettyFormula(form))
    println(Printer.prettyFormula(form2))


    assert(!isSame(form, form2))

  }
   
  test("Verifying predicates on instantiatePredicateSchemas") {
    val f = constant_symbol("f", Seq(x, y)) // \u, v. f(u, v), f(x, y)
    val g = schematic_symbol("g", Seq(f, z)) // \u, v. g(u, v), g(f(x, y), z)
    val h = constant_symbol("h", Seq(g, w)) // \u, v. h(u, v), h(g(f(x, y), z), w)
    val t = instantiatePredicateSchemas(h, Map[SchematicVarOrPredLabel, LambdaTermFormula](
      SchematicFunctionLabel("f", 2) -> LambdaFormulaTerm(Seq(xl, yl), u),
      SchematicFunctionLabel("g", 1) -> LambdaFormulaTerm(Seq(xl), u),
      SchematicFunctionLabel("test", 1)  -> LambdaFormulaTerm(Seq(xl), u)
    )) // h(g(f(x, y), w), w)

    assert(isSame(t, h))

  }

  test("Verifying instantiateConnectorSchemas on Connectors") {
    val f = ConstantPredicateLabel("F", 1) // \u, v. f(u, v)
    val g = ConstantPredicateLabel("G", 1) // \u, v. g(u, v)
    val h = SchematicConnectorLabel("conn", 2) // \u, v. h(u, v)
    val t = instantiateConnectorSchemas(h(f(a), g(b)), Map[SchematicConnectorLabel, LambdaTermFormula](
      

    )) // h(f(a), g(b))

    assert(isSame(t, h))
  }

  test("Verifying instantiatePredicateSchemas & instantiateConnectorSchemas on Binders") {

  }
  
  test("Verifying instantiateTermSchemas") {

  }
}
