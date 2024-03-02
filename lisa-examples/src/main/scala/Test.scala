object Test extends lisa.Main {
  import lisa.automation.atp.Goeland

  draft()

  val u = variable
  val v = variable
  val w = variable
  val x = variable
  val y = variable
  val z = variable
  val a = variable
  val c = variable
  val d = variable

  val f = function[1]
  val g = function[1]
  val h = function[2]

  val p = formulaVariable
  val q = formulaVariable
  val r = formulaVariable

  val E = predicate[2]
  val P = predicate[2]
  val Q = predicate[1]
  val R = predicate[1]
  val s = predicate[1]
  val t = predicate[1]

  val assump1 = ∀(u, ∀(v, ∀(w, E(u, v) ==> (E(v, w) ==> E(u, w)))))
  val assump2 = ∀(x, ∀(y, E(x, y) ==> (E(f(x), f(y)))))
  val assump3 = ∀(z, E(f(g(z)), g(f(z))))

  val goal = E(f(f(g(a))), g(f(f(a))))

  val gothm0 = Theorem((p /\ q) \/ (p /\ r) |- (p /\ (q \/ r))) {
    have(thesis) by Goeland("goeland/Test.gothm0_sol")
  }

  val gothm1 = Theorem((p /\ (q \/ r)) |- (p /\ q) \/ (p /\ r)) {
    have(thesis) by Goeland("goeland/Test.gothm1_sol")
  }

  val gothm2 = Theorem((Q(x), Q(x) ==> R(y)) |- R(y)) {
    have(thesis) by Goeland("goeland/Test.gothm2_sol")
  }

  val gothm3 = Theorem(!s(∅) ==> !forall(x, s(x))) {
    have(thesis) by Goeland("goeland/Test.gothm3_sol")
  }

  val gothm4 = Theorem(() |- ∃(x, ∀(y, Q(x) ==> Q(y)))) {
    have(thesis) by Goeland("goeland/Test.gothm4_sol")
  }

  val gothm5 = Theorem(∀(x, E(x, x)) |- ∀(x, E(f(x), f(x)))) {
    have(thesis) by Goeland//("goeland/Test.gothm5_sol")
  }

  val gothm6 = Theorem(∀(y, ∀(x, E(x, y))) |- ∀(y, ∀(x, E(f(x), h(x, y))))) {
    have(thesis) by Goeland//("goeland/Test.thm6_sol")
  }

}
