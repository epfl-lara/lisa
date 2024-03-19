object HOLTest extends lisa.HOL{
  import lisa.maths.settheory.types.ADTTactic.*
  import lisa.maths.settheory.types.ADTSyntax.*

  val typ = variable

  val define(list: ADT, constructors(nil, cons)) = () | (typ, list)

  val typecheckNil = TypingTheorem(nil(𝔹) :: list(𝔹))
  val typecheckCons = TypingTheorem(cons(𝔹) :: (𝔹 |=> (list(𝔹) |=> list(𝔹))))
  }