object ADTExample extends lisa.Main {
  import lisa.maths.settheory.types.adt.{*, given}

  // variable declarations
  val A = variable
  val B = variable
  val C = variable

  val x0 = variable
  val x1 = variable
  val y0 = variable
  val y1 = variable

  val l = variable
  val x = variable
  val y = variable

  val opt = variable
  val P = predicate[1]

  
  // Examples of ADT

  // Product type with only constructor pair :: A -> B -> A * B
  val define(product, constructors(pair)) = (A, B)

  // Sum type with constructors left :: A -> A + B and right :: B -> A + B
  val define(sum, constructors(left, right)) = A | B 

  // Boolean type with two constructors: true :: bool and false :: bool
  val define(bool, constructors(tru, fals)) = () | ()

  // Unit type with only one constructor (and value): u :: unit
  val define(unit, constructors(u)) = ()

  // Empty type with no constructors 
  val define(nothing, constructors()) = None

  // Option type with two constructors: none :: Option A and some :: A -> Option A
  val define(option, constructors(none, some)) = () | A

  // Natural numbers with two constructors: zero :: int and succ :: int -> int
  val define(nat: ADT, constructors(zero, succ)) = () | nat

  // List type with two constructors: nil :: list A and cons :: A -> list A -> list A
  val define(list: ADT, constructors(nil, cons)) = () | (A, list)

  // SyntacticFunction("altSucc", nat.underlying.underlying, Map(zero.underlying.underlying -> (altSucc => zero), succ.underlying.underlying -> (altSucc => succ * altSucc * x0)), nat, Seq())

  // //Example of theorem on lists using introduction rules, injectivity of constructors and structural induction
  lazy val consInj = Theorem((l :: list(A), x :: A) |- !(l === cons * x * l)) { sp ?=>
    val typeNil = have(nil(A) :: list(A)) by TypeChecker.prove
    val typeCons = have((y :: A, l :: list(A)) |- cons(A) * y * l :: list(A)) by TypeChecker.prove

    have(forall(l, l :: list(A) ==> forall(x, x :: A ==> !(l === cons(A) * x * l)))) by Induction(list){
      Case(nil) subproof {
        have(x :: A ==> !(nil(A) === cons(A) * x * nil(A))) by Tautology.from(list.injectivity(nil, cons) of (y0 := x, y1 := nil(A)), typeNil)
        thenHave(forall(x, x :: A ==> !(nil(A) === cons(A) * x * nil(A)))) by RightForall
      }
      Case(cons, y, l) subproof {
        have((y :: A ==> !(l === cons(A) * y * l), y :: A, l :: list(A)) |- x :: A ==> !(cons(A) * y * l === cons(A) * x * (cons(A) * y * l))) by Tautology.from(
             cons.injectivity of (x0 := y, x1 := l, y0 := x, y1 := cons(A) * y * l),
             typeCons
           )
        thenHave((y :: A ==> !(l === cons(A) * y * l), y :: A, l :: list(A)) |- forall(x, x :: A ==> !(cons(A) * y * l === cons(A) * x * (cons(A) * y * l)))) by RightForall
        thenHave((forall(x, x :: A ==> !(l === cons(A) * x * l)), y :: A, l :: list(A)) |- forall(x, x :: A ==> !(cons(A) * y * l === cons(A) * x * (cons(A) * y * l)))) by LeftForall
      }
    }
    
    thenHave(l :: list(A) ==> forall(x, x :: A ==> !(l === cons(A) * x * l))) by InstantiateForall(l)
    thenHave(l :: list(A) |- forall(x, x :: A ==> !(l === cons(A) * x * l))) by Tautology
    thenHave(l :: list(A) |- x :: A ==> !(l === cons(A) * x * l)) by InstantiateForall(x)
    thenHave(thesis) by Tautology
  }



  val not = fun(bool, bool) {
    Case(tru) { fals }
    Case(fals) { tru }
  }

  Theorem(x :: bool |- not * (not * x) === x) {
    have(forall(x, x :: bool ==> (not * (not * x) === x))) by Induction(bool) {
      Case(tru) subproof {
        val notFals = have(not * fals === tru) by Restate.from((not.elim(fals)))
        have(fals === not * tru) by Restate.from(not.elim(tru))
        have(not * (not * tru) === tru) by Substitution.ApplyRules(lastStep)(notFals)
      }
      Case(fals) subproof {
        val notTrue = have(not * tru === fals) by Restate.from((not.elim(tru)))
        have(tru === not * fals) by Restate.from(not.elim(fals))
        have(not * (not * fals) === fals) by Substitution.ApplyRules(lastStep)(notTrue)
      }
    }
    have(x :: bool ==> (not * (not * x) === x)) by InstantiateForall(x)(lastStep)

  }

  // val pred = fun(nat, nat) {
  //   Case(zero) { zero}
  //   Case(succ, x) { x }
  // }

  // val length: ADTFunction = fun(list, nat) {
  //   Case(nil) { zero }
  //   Case(cons, x, l) { succ * (length * l) }
  // }

// }

// object FunctionExample extends lisa.Main {
//   import lisa.maths.settheory.types.adt.*

//   draft()  

//   val x = variable

//   val define(bool, constructors(tru, fals)) = () | ()




//   //   val hyp = have(not() * (not() * x) === x |- not() * (not() * x) === x) by Hypothesis
//   //   thenHave((x === fals(), not() * fals() * fals() === fals()) |- not() * x * x === x) by LeftSubstEq.withParametersSimple(List(x -> fals()), lambda(x, not() * (not() * x) === x))

    

//   //   println(bool.patternMatching.statement)
    
//   //   println(not.shortDefinition(fals).statement)
//   //   sorry 
//   // }

}