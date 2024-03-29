


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
  import ADTSyntax.*

  // Type variable
  val A = variable

  // Defining polymorphic lists with two constructors: nil taking no arguments, representing the empty list,
  // and cons taking an element and a list, representing the prepending of an element to a list.
  val define(list: ADT, constructors(nil, cons)) = () | (A, list)

  val typecheckNil = TypingTheorem(nil(𝔹) :: list(𝔹))
  val typecheckCons = TypingTheorem(cons(𝔹) :: (𝔹 |=> (list(𝔹) |=> list(𝔹))))

}
