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

  test("Substituting simultaneously terms that reference each others (2) (expansion explosion)") {

    val f = constant_symbol("f", Seq(x, y))  // \u, v. f(u, v), f(x, y)
    val g = schematic_symbol("g",Seq(f, x)) // \u, v. g(u, v), g(f(x, y), x)
    
    val t = instantiateTermSchemas(g, Map(
      xl  -> LambdaTermTerm(Nil, f),
      SchematicFunctionLabel("g", 2) -> LambdaTermTerm(Seq(ul, vl), Term(ConstantFunctionLabel("g", 2), Seq(u, v)))
    )) 
    
    assert(isSame(t, constant_symbol("g", Seq(constant_symbol("f", Seq(f, y)), f))))
  }
}
