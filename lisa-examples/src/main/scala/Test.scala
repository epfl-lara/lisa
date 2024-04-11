import lisa.maths.settheory.types.TypeLib.|=>

object Test extends lisa.Main {

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

  val E = predicate[2]
  val P = predicate[2]

  val assump1 = ∀(u, ∀(v, ∀(w, E(u, v) ==> (E(v, w) ==> E(u, w)))))
  val assump2 = ∀(x, ∀(y, E(x, y) ==> (E(f(x), f(y)))))
  val assump3 = ∀(z, E(f(g(z)), g(f(z))))

  val goal = E(f(f(g(a))), g(f(f(a))))


  val thm = Theorem((assump1, assump2, assump3) |- goal) {
    have(thesis) by Tableau
  }

  val thm1 = Theorem(∀(x, E(x, x)) |- ∀(x, E(f(x), f(x)))) {
    val s1 = assume(∀(x, E(x, x)))
    have(thesis) by RightForall(s1 of f(x))
  }

  val thm2 = Theorem(∀(y, ∀(x, E(x, y))) |- ∀(y, ∀(x, E(f(x), h(x, y))))) {
    val s1 = assume(∀(y, ∀(x, E(x, y))))
    println((s1 of (h(x, y), f(x))).result)
    have(∀(x, E(f(x), h(x, y)))) by RightForall(s1 of (h(x, y), f(x)))
    thenHave(thesis) by RightForall
  }

  val thm3 = Theorem(∀(y, ∀(x, E(x, y))) |- E(f(x), y) /\ E(x, h(x, y))) {
    val s1 = assume(∀(y, ∀(x, E(x, y))))
    val s2 = have(∀(x, E(x, y))) by Restate.from(s1 of y)
    have(thesis) by Tautology.from(s2 of f(x), s2 of (x, y := h(x, y)))

  }

  val ax = Axiom(∀(x, ∀(y, P(x, y))))
  val thm4 = Theorem(c === d) {
    have(thesis) by Restate.from(ax of (c, d, P := ===))
    showCurrentProof()
  }

}
