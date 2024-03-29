
import lisa.automation.Exact

object ITP2024_Examples extends lisa.HOL {

  ///////////////////////////
  /////////// HOL ///////////
  ///////////////////////////

  val x = typedvar(𝔹)
  val y = typedvar(𝔹)
  val f = typedvar(𝔹 |=> 𝔹)
  val g = typedvar(𝔹 |=> (𝔹 |=> 𝔹))
  val h = typedvar((𝔹 |=> 𝔹) |=> 𝔹)




  // :: is equivalent to ∈
  val typecheckTest = Theorem(λ(h,  λ(f, f*(x)) =:= h) :: (((𝔹 |=> 𝔹) |=> 𝔹) |=> 𝔹) ) {
    have(thesis) by TypeCheck
  }

  val doubleBeta = Theorem(λ(x, λ(x, y)*x)*y =:= y){
    val s1 = have(BETA(λ(x, λ(x, y)*x)*x)) // λ(x, λ(x, y)*x)*x === λ(x, y)*x
    val s2 = have(INST(Seq((x, y)), s1)) // λ(x, λ(x, y)*x)*y === λ(x, y)*y
    val s3 = have(BETA(λ(x, y)*x)) // λ(x, y)*x =:= y
    val s4 = have(INST(Seq((x, y)), s3)) // λ(x, y)*y =:= y
    have(_TRANS(s2, s4))
  }

    

  ////////////////////////////
  /////////// ADTs ///////////
  ////////////////////////////


  import lisa.maths.settheory.types.ADTTactic.*
  import lisa.fol.FOL.*
  import ADTSyntax.*
  import lisa.prooflib.SimpleDeducedSteps.*


  // Type variable
  val A = variable

  // Defining polymorphic lists with two constructors: nil taking no arguments, representing the empty list,
  // and cons taking an element and a list, representing the prepending of an element to a list.
  val define(list: ADT, constructors(nil, cons)) = () | (A, list)

  // Theorem: nil(𝔹) has type list(𝔹)
  val typecheckNil = Theorem(nil(𝔹) :: list(𝔹)) {
    have(forall(A, nil(A) :: list(A))) by Restate.from(nil.typing)
    thenHave(thesis) by InstantiateForall(𝔹)
  }

  // Theorem: cons(𝔹) has type 𝔹 -> list(𝔹) -> list(𝔹)
  val typecheckCons = Theorem(cons(𝔹) :: (𝔹 |=> (list(𝔹) |=> list(𝔹)))) {
    have(forall(A, cons(A) :: (A |=> (list(A) |=> list(A))))) by Restate.from(cons.typing)
    thenHave(thesis) by InstantiateForall(𝔹)
  }


  val a = typedvar(A)
  val l1 = typedvar(list(A))
  val l2 = typedvar(list(A))

  // Theorem: Two lists with the same head are equal if and only if their tails are equal
  val prependSameElement = Theorem((cons(A) * a * l1 === cons(A) * a * l2) <=> (l1 === l2)) {
    have((cons(A) * a * l1 === cons(A) * a * l2) <=> ((a === a) /\ (l1 === l2))) by Exact(cons.injectivity1 of (x := a)) 
    thenHave(thesis) by Weakening
  }

}
