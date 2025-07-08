object ADTExample extends lisa.Main {
  /*
  import lisa.maths.settheory.types.adt.{*, given}

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

  Lemma(nil(A) :: list(A)) {
    have(thesis) by TypeChecker.prove
  }
  Lemma((x :: A, l :: list(A)) |- cons(A) * x * l :: list(A)) {
    have(thesis) by TypeChecker.prove
  }

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

  // ************************
  // * 4 : Induction Tactic *
  // ************************

  Theorem(x :: bool |- not * (not * x) === x) {
    have(thesis) by Induction() {
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
  }

  // ****************************
  // * 5: All features together *
  // ****************************

  val consInj = Theorem((l :: list(A), x :: A) |- !(l === cons(A) * x * l)) {

    val typeNil = have(nil(A) :: list(A)) by TypeChecker.prove
    val typeCons = have((y :: A, l :: list(A)) |- cons(A) * y * l :: list(A)) by TypeChecker.prove

    have(l :: list(A) |- forall(x, x :: A ==> !(l === cons(A) * x * l))) by Induction() {
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

    thenHave(l :: list(A) |- x :: A ==> !(l === cons(A) * x * l)) by InstantiateForall(x)
    thenHave(thesis) by Tautology
  }
   */
}
