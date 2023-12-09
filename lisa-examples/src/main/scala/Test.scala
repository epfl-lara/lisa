
object Test extends lisa.Main {

  val u = variable
  val v = variable
  val w = variable
  val x = variable
  val y = variable
  val z = variable
  val a = variable

  val f = function[1]
  val g = function[1]

  val E = predicate[2]

  val assump1 = ∀(u, ∀(v, ∀(w, E(u, v) ==> (E(v, w) ==> E(u, w)))))
  val assump2 = ∀(x, ∀(y, E(x, y) ==> (E(f(x), f(y)))))
  val assump3 = ∀(z, E(f(g(z)), g(f(z))))

  val goal = E(f(f(g(a))), g(f(f(a))))

  println(K.prettySCProof(Tableau.solve((assump1, assump2, assump3) |- goal).get))

  
  val thm = Theorem((assump1, assump2, assump3) |- goal) {
    have(thesis) by Tableau
  }

}
