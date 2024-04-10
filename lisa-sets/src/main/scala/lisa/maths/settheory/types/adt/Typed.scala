package lisa.maths.settheory.types.adt

import lisa.maths.settheory.SetTheory.{*, given}
import lisa.maths.settheory.types.TypeLib.{any}
import lisa.maths.settheory.types.TypeSystem.{TypedConstantFunctional, FunctionalClass}

def typeArity(cons: SemanticConstructor) = cons.typeArity


class Constructor(using line: sourcecode.Line, file: sourcecode.File)(
  val underlying: SemanticConstructor
  ) extends TypedConstantFunctional(
      underlying.fullName, 
      typeArity(underlying), 
      FunctionalClass(Seq.fill(underlying.typeArity)(any), underlying.typeVariables, underlying.typ, underlying.typeArity), 
      underlying.intro) {

  val name = underlying.fullName
  val intro = 
    THM(underlying.intro.statement, s"${name} introduction rule", line.value, file.value, Theorem){
      have(underlying.intro)
    }
  lazy val injectivity = 
    THM(underlying.injectivity.statement, s"${name} injectivity", line.value, file.value, Theorem){
      have(underlying.injectivity)
    }
  val typeVariables: Seq[Variable] = underlying.typeVariables
  def apply(args: Term*) = applySeq(args)

}

class ADT(using line: sourcecode.Line, file: sourcecode.File)(
  val underlying: SemanticADT, 
  val constructors: Seq[Constructor]
  ) {

  val name = underlying.name
  lazy val induction = 
    THM(underlying.induction.statement, s"${name} structural induction principle", line.value, file.value, Theorem){
      have(underlying.induction)
    }
  lazy val elim = 
    THM(underlying.elim.statement, s"${name} elimination rule", line.value, file.value, Theorem){
      have(underlying.elim)
    }
  def injectivity(c1: Constructor, c2: Constructor) = 
    val injectivityLemma = underlying.injectivity(c1.underlying, c2.underlying)
    THM(injectivityLemma.statement, s"${c1.name}-${c2.name} injectivity", line.value, file.value, Theorem){
      have(injectivityLemma)
    }
  val typeVariables: Seq[Variable] = underlying.typeVariables
  def apply(args: Term*) = underlying.term(args)
}

def typeArity(fun: SemanticFunction) = fun.typeArity

class ADTFunction(using line: sourcecode.Line, file: sourcecode.File)(
  private[adt] val underlying: SemanticFunction,
  val adt: ADT,
  ) extends TypedConstantFunctional(
    underlying.fullName, 
    typeArity(underlying), 
    FunctionalClass(Seq.fill(underlying.typeArity)(any), underlying.typeVariables, underlying.typ, underlying.typeArity), 
    underlying.intro) {

  val name = underlying.fullName

  val elim: Map[Constructor, THM] = adt.constructors.map(c => 
      (c, THM(underlying.shortDefinition(c.underlying).statement, s"${name} elimination rule: ${c.name} case", line.value, file.value, Theorem){
        have(underlying.shortDefinition(c.underlying))
      })
    ).toMap

  val shortDefinition = elim
  
  val intro = 
    THM(underlying.intro.statement, s"${name} introduction rule", line.value, file.value, Theorem){
      have(underlying.intro)
    }

  val typeVariables = underlying.typeVariables
  def apply(terms: Term*) = applySeq(terms)

}

// /**
//   * Instantiates the type variables of this function with given terms.
//   *
//   * @param terms the terms to instantiate the type variables with
//   */
// 


