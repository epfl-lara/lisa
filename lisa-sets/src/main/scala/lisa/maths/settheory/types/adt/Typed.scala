package lisa.maths.settheory.types.adt

import lisa.maths.settheory.SetTheory.{*, given}
import lisa.maths.settheory.types.TypeLib.{any}
import lisa.maths.settheory.types.TypeSystem.{TypedConstantFunctional, FunctionalClass}



class Constructor[N <: Arity](using line: sourcecode.Line, file: sourcecode.File)(
  val underlying: SemanticConstructor[N]
  ) extends TypedConstantFunctional[N](
      underlying.fullName, 
      underlying.typeArity, 
      FunctionalClass(Seq.fill(underlying.typeArity)(any), underlying.typeVariablesSeq, underlying.typ, underlying.typeArity), 
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
  val typeVariables: Variable ** N = underlying.typeVariables

}



class ADT[N <: Arity](using line: sourcecode.Line, file: sourcecode.File)(
  val underlying: SemanticADT[N], 
  val constructors: Seq[Constructor[N]]
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
  def injectivity(c1: Constructor[N], c2: Constructor[N]) = 
    val injectivityLemma = underlying.injectivity(c1.underlying, c2.underlying)
    THM(injectivityLemma.statement, s"${c1.name}-${c2.name} injectivity", line.value, file.value, Theorem){
      have(injectivityLemma)
    }
  val typeVariables: Variable ** N = underlying.typeVariables

  def applyUnsafe(args: Term ** N): Term = underlying.term(args.toSeq)
  def applySeq(args: Seq[Term]): Term = underlying.term(args)
  //def apply(args: Term*): Term = underlying.term(args)
}

class ADTFunction[N <: Arity](using line: sourcecode.Line, file: sourcecode.File)(
  private[adt] val underlying: SemanticFunction[N],
  val adt: ADT[N],
  ) extends TypedConstantFunctional[N](
    underlying.fullName, 
    underlying.typeArity, 
    FunctionalClass(Seq.fill(underlying.typeArity)(any), underlying.typeVariablesSeq, underlying.typ, underlying.typeArity), 
    underlying.intro) {

  val name = underlying.fullName

  val elim: Map[Constructor[N], THM] = adt.constructors.map(c => 
      (c, THM(underlying.shortDefinition(c.underlying).statement, s"${name} elimination rule: ${c.name} case", line.value, file.value, Theorem){
        have(underlying.shortDefinition(c.underlying))
      })
    ).toMap

  val shortDefinition = elim
  
  val intro = 
    THM(underlying.intro.statement, s"${name} introduction rule", line.value, file.value, Theorem){
      have(underlying.intro)
    }

  val typeVariables: Variable ** N = underlying.typeVariables
}

// /**
//   * Instantiates the type variables of this function with given terms.
//   *
//   * @param terms the terms to instantiate the type variables with
//   */
// 


