package lisa

import lisa.SetTheoryLibrary
import lisa.prooflib.BasicMain

/**
 * The parent trait of all theory files containing mathematical development
 */
trait HOL extends BasicMain {
  export lisa.maths.settheory.types.TypeSystem.*
  export lisa.maths.settheory.types.TypeLib.{any, Zero, One, 𝔹, |=>}
  export TypeChecker.*
  export lisa.hol.VarsAndFunctions.{main => _, given, *}
  export SetTheoryLibrary.{*, given}
  val STL = SetTheoryLibrary
  val F: lisa.fol.FOL.type = lisa.fol.FOL
  export F.{Term, variable, given}


  private val A = variable

  val =:= : TypedConstantFunctional[1] ={
    val =:= =  F.ConstantFunctionLabel.infix("=:=", 1)
    addSymbol(=:=)
    val typing_of_eq = Axiom(F.forall(A, =:=(A) :: (A |=> (A |=> 𝔹))))
    TypedConstantFunctional[1]("=:=", 1, FunctionalClass(Seq(any), Seq(A), (A |=> (A |=> 𝔹)), 1), typing_of_eq)
  }

  val holeq : TypedConstantFunctional[1] = =:=

  extension (t1:Term) {
    def =:=(t2:Term): Term = 
      val A = computeType(t1)
      if (A == computeType(t2)) 
        holeq.applySeq(Seq(A))*(t1)*(t2) 
      else 
        throw new TypingException("in expression " + t1 + " =:= " + t2 + " the types " + A + "of left-hand side and " + computeType(t2) + " of right-hand side do not match.")
    def equalityOfType(A:Term) (t2:Term): Term = holeq.applySeq(Seq(A))*(t1)*(t2) //compute A with computeType, possibly.
  }



  

}