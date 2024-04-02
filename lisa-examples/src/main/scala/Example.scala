
object ITP2024_HOL_Examples extends lisa.HOL {

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

}

  ////////////////////////////
  /////////// ADTs ///////////
  ////////////////////////////

object ITP2024_ADT_Examples extends lisa.Main {
  import lisa.maths.settheory.types.ADTTactic.*
  import lisa.maths.settheory.types.TypeSystem.*
  import ADTSyntax.*

  // variable declarations
  val A = variable
  val B = variable
  val C = variable

  val a0 = variable
  val a1 = variable
  val b0 = variable
  val b1 = variable

  val l = variable
  val x = variable
  val y = variable

  val opt = variable
  val P = predicate[1]

  
  // Examples of ADT

  // Product type with only constructor pair :: A -> B -> A * B
  val define(product: ADT, constructors(pair)) = (A, B)

  // Sum type with constructors left :: A -> A + B and right :: B -> A + B
  val define(sum: ADT, constructors(left, right)) = A | B 

  // Boolean type with two constructors: true :: bool and false :: bool
  val define(bool: ADT, constructors(tru, fals)) = () | ()

  // Unit type with only one constructor (and value): u :: unit
  val define(unit, constructors(u)) = ()

  // Empty type with no constructors 
  val define(nothing: ADT, constructors()) = None

  // Option type with two constructors: none :: Option A and some :: A -> Option A
  val define(option: ADT, constructors(none, some)) = () | A

  // Natural numbers with two constructors: zero :: int and succ :: int -> int
  val define(int: ADT, constructors(zero, succ)) = () | int

  // List type with two constructors: nil :: list A and cons :: A -> list A -> list A
  val define(list: ADT, constructors(nil, cons)) = () | (A, list)

  
  // Example of theorem on lists using introduction rules, injectivity of constructors and structural induction
  // Theorem: l != cons * x * l for any x of type A and list l of A
  val listNeqPrepend = Theorem((l :: list(A), x :: A) |- !(l === cons(A) * x * l)) {
    val typeNil = have(nil(A) :: list(A)) by TypeChecker.prove
    val typeCons = have((y :: A, l :: list(A)) |- cons(A) * y * l :: list(A)) by TypeChecker.prove
    have(x :: A ==> !(nil(A) === cons(A) * x * nil(A))) by Tautology.from(list.injectivity(nil, cons) of (b0 := x, b1 := nil(A)), typeNil)
    val baseCase = thenHave(forall(x, x :: A ==> !(nil(A) === cons(A) * x * nil(A)))) by RightForall

    have((y :: A ==> !(l === cons(A) * y * l), y :: A, l :: list(A)) |- x :: A ==> !(cons(A) * y * l === cons(A) * x * (cons(A) * y * l))) by Tautology.from(
      cons.injectivity of (a0 := y, a1 := l, b0 := x, b1 := cons(A) * y * l),
      typeCons
    )
    thenHave((y :: A ==> !(l === cons(A) * y * l), y :: A, l :: list(A)) |- forall(x, x :: A ==> !(cons(A) * y * l === cons(A) * x * (cons(A) * y * l)))) by RightForall
    thenHave((forall(x, x :: A ==> !(l === cons(A) * x * l)), y :: A, l :: list(A)) |- forall(x, x :: A ==> !(cons(A) * y * l === cons(A) * x * (cons(A) * y * l)))) by LeftForall
    thenHave(y :: A |- l :: list(A) ==> (forall(x, x :: A ==> !(l === cons(A) * x * l)) ==>  forall(x, x :: A ==> !(cons(A) * y * l === cons(A) * x * (cons(A) * y * l))))) by Tautology
    thenHave(y :: A |- forall(l, l :: list(A) ==> (forall(x, x :: A ==> !(l === cons(A) * x * l)) ==>  forall(x, x :: A ==> !(cons(A) * y * l === cons(A) * x * (cons(A) * y * l)))))) by RightForall
    thenHave(y :: A ==> forall(l, l :: list(A) ==> (forall(x, x :: A ==> !(l === cons(A) * x * l)) ==>  forall(x, x :: A ==> !(cons(A) * y * l === cons(A) * x * (cons(A) * y * l)))))) by Restate
    val inductiveCase = thenHave(forall(y, y :: A ==> forall(l, l :: list(A) ==> (forall(x, x :: A ==> !(l === cons(A) * x * l)) ==>  forall(x, x :: A ==> !(cons(A) * y * l === cons(A) * x * (cons(A) * y * l))))))) by RightForall

    have(forall(l, l :: list(A) ==> forall(x, x :: A ==> !(l === cons(A) * x * l)))) by Tautology.from(
      list.induction of (P := lambda(l, forall(x, x :: A ==> !(l === cons(A) * x * l)))), 
      baseCase,
      inductiveCase,
    )
    
    thenHave(l :: list(A) ==> forall(x, x :: A ==> !(l === cons(A) * x * l))) by InstantiateForall(l)
    thenHave(l :: list(A) |- forall(x, x :: A ==> !(l === cons(A) * x * l))) by Tautology
    thenHave(l :: list(A) |- x :: A ==> !(l === cons(A) * x * l)) by InstantiateForall(x)
    thenHave(thesis) by Tautology
  }

}
