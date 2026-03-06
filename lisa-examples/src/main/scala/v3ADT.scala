object v3ADT extends lisa.Main {


  import lisa.maths.SetTheory.Types.ADT.{*, given}
  
  draft()
  withCache()

  // variable declarations
  val A = variable

  val n = variable
  val l = variable
  val x = variable
  val y = variable

  val x0 = variable
  val x1 = variable
  val y0 = variable
  val y1 = variable

  // ***********************
  // * 1 : Examples of ADT *
  // ***********************

  // Boolean
  val define(bool: ADT[0], constructors(tru, fals)) = () | ()

  // Nat
  val define(nat: ADT[0], constructors(zero, succ)) = () | nat

  // Option
  val define(option: ADT[1], constructors(none, some)) = A --> () | A

  // List
  val define(list: ADT[1], constructors(nil, cons)) = A --> () | (A, list)

  // Nothing
  val define(nothing, constructors()) = |

  // ****************
  // * 2 : Theorems *
  // ****************

  // Injectivity
  show(nil.injectivity)
  show(cons.injectivity)
  show(list.injectivity(nil, cons))

  // Introduction rules
  show(nil.intro)
  show(cons.intro)


  // Induction
  show(list.induction)

  // Pattern matching
  show(list.elim)

  // *****************
  // * 3 : Functions *
  // *****************

  val not = fun(bool, bool) {
    Case(tru) { fals }
    Case(fals) { tru }
  }

  val pred = fun(nat, nat):
    Case(zero):
      zero
    Case(succ, n):
      n

}
