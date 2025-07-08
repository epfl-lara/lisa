package lisa.test.automation

import lisa.SetTheoryLibrary.{_, given}
import lisa.automation.Substitution.*
import lisa.automation.Tableau.*
import lisa.utils.fol.FOL.*
import lisa.utils.prooflib.Exports.*
import lisa.utils.K.SCProofChecker.checkSCProof
// import lisa.utils.parsing.FOLPrinter.prettyFormula
// import lisa.utils.parsing.FOLPrinter.prettySCProof
// import lisa.utils.parsing.FOLPrinter.prettyTerm
import org.scalatest.funsuite.AnyFunSuite

class TableauTest extends AnyFunSuite {

  /*
  test(s"Propositional Positive cases (${posi.size})") {
    assert(posi.forall(_._3), posi.map((i, f, b, proof, judg) => s"$i $b" + (if !b then s" $f" else "")).mkString("\n"))
    if posi.exists(tup => tup._5.nonEmpty & !tup._5.get.isValid) then
      fail("A proof is wrong: " + posi.map(tup => if tup._5.nonEmpty & !tup._5.get.isValid then prettySCProof(tup._5.get) + "\n").mkString("\n"))
  }

  test(s"First Order Quantifier Free Positive cases (${posqf.size})") {
    assert(posqf.forall(_._3), posqf.map((i, f, b, proof, judg) => (s"$i $b" + (if !b then s" $f" else ""))).mkString("\n"))
    if posqf.exists(tup => tup._5.nonEmpty & !tup._5.get.isValid) then
      fail("A proof is wrong: " + posi.map(tup => if tup._5.nonEmpty & !tup._5.get.isValid then prettySCProof(tup._5.get) + "\n").mkString("\n"))
  }

  test(s"First Order Easy Positive cases (${poseasy.size})") {
    assert(poseasy.forall(_._3), poseasy.map((i, f, b, proof, judg) => (s"$i $b" + (if !b then s" $f" else ""))).mkString("\n"))
    if poseasy.exists(tup => tup._5.nonEmpty & !tup._5.get.isValid) then
      fail("A proof is wrong: " + posi.map(tup => if tup._5.nonEmpty & !tup._5.get.isValid then prettySCProof(tup._5.get) + "\n").mkString("\n"))
  }

  test(s"First Order Hard Positive cases (${poshard.size})") {
    assert(poshard.forall(_._3), poshard.map((i, f, b, proof, judg) => (s"$i $b" + (if !b then s" $f" else ""))).mkString("\n"))
    if poshard.exists(tup => tup._5.nonEmpty & !tup._5.get.isValid) then
      fail("A proof is wrong: " + posi.map(tup => if tup._5.nonEmpty & !tup._5.get.isValid then prettySCProof(tup._5.get) + "\n").mkString("\n"))
  }

}
object TableauTest {

  val u = variable[Ind]
  val w = variable[Ind]
  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]

  val a = variable[Prop]
  val b = variable[Prop]
  val c = variable[Prop]
  val d = variable[Prop]
  val e = variable[Prop]

  val f = variable[Ind >>: Ind]
  val g = variable[Ind >>: Ind]
  val h = variable[Ind >>: Ind >>: Ind]

  val D = variable[Ind >>: Prop]
  val E = variable[Ind >>: Ind >>: Prop]
  val P, Q = variable[Ind >>: Prop]
  val R = variable[Ind >>: Ind >>: Prop]

  var doprint: Boolean = false
  def printif(s: Any) = if doprint then println(s) else ()

  val posi = List(
    a <=> a,
    a \/ !a,
    ((a ==> b) /\ (b ==> c)) ==> (a ==> c),
    (a <=> b) <=> ((a /\ b) \/ (!a /\ !b)),
    ((a ==> c) /\ (b ==> c)) <=> ((a \/ b) ==> c),
    ((a ==> b) /\ (c ==> d)) ==> ((a \/ c) ==> (b \/ d))
  ).zipWithIndex.map(f =>
    val res = solve(() |- f._1)
    (f._2, f._1, res.nonEmpty, res, res.map(checkSCProof))
  )

  // Quantifier Free

  val posqf = List(
    posi.map(fo => fo._2.substitute(a := P(h(x)(h2)), b := P(x), c := R(x)(h(x)(h2)))),
    posi.map(fo => fo._2.substitute(a := P(h(x)(h2)), b := P(h(x)(h2)), c := R(x)(h(x)(h2))))),
    posi.map(fo => fo._2.substitute(a := R(y)(y), b := P(h(y)(h2)), c := R(h(x)(y))(h2))))
  ).flatten.zipWithIndex.map(f =>
    val res = solve(() |- f._1)
    (f._2, f._1, res.nonEmpty, res, res.map(checkSCProof))
  )

  // First Order Easy

  val poseasy = List(
    posi.map(fo => fo._2.substitute(a := forall(x, P(x)), b := forall(x, P(y)), c := exists(x, P(x)))),
    posi.map(fo => fo._2.substitute(a := forall(x, P(x) /\ Q(f(x))), b := forall(x, P(x) \/ R(y)(x)), c := exists(x, Q(x) ==> R(x)(y)))),
    posi.map(fo => fo._2.substitute(a := exists(y, forall(x, P(x) /\ Q(f(y)))), b := forall(y, exists(x, P(x) \/ R(y)(x))), c := forall(y, exists(x, Q(x) ==> R(x)(y)))))
  ).flatten.zipWithIndex.map(f =>
    val res = solve(() |- f._1)
    (f._2, f._1, res.nonEmpty, res, res.map(checkSCProof))
  )

  // First Order Hard, from https://isabelle.in.tum.de/library/FOL/FOL-ex/Quantifiers_Cla.html

  val a1 = forall(x, forall(y, forall(z, ((E(x)(y) /\ E(y)(z)) ==> E(x)(z)))))
  val a2 = forall(x, forall(y, (E(x)(y) ==> E(f(x))(f(y)))))
  val a3 = forall(x, E(f(g(x)))(g(f(x))))
  val biga = forall(
    x,
    forall(
      y,
      forall(
        z,
        ((E(x)(y) /\ E(y)(z)) ==> E(x)(z)) /\
          (E(x)(y) ==> E(f(x))(f(y))) /\
          E(f(g(x)))(g(f(x)))
      )
    )
  )

  val poshard = List(
    forall(x, P(x) ==> Q(x)) ==> (forall(x, P(x)) ==> forall(x, Q(x))),
    forall(x, forall(y, R(x)(y))) ==> forall(y, forall(x, R(x)(y))),
    forall(x, forall(y, R(x)(y))) ==> forall(y, forall(x, R(y)(x))),
    exists(x, exists(y, R(x)(y))) ==> exists(y, exists(x, R(x)(y))),
    exists(x, exists(y, R(x)(y))) ==> exists(y, exists(x, R(y)(x))),
    (forall(x, P(x)) \/ forall(x, Q(x))) ==> forall(x, P(x) \/ Q(x)),
    forall(x, a ==> Q(x)) <=> (a ==> forall(x, Q(x))),
    forall(x, P(x) ==> a) <=> (exists(x, P(x)) ==> a),
    exists(x, P(x) \/ Q(x)) <=> (exists(x, P(x)) \/ exists(x, Q(x))),
    exists(x, P(x) /\ Q(x)) ==> (exists(x, P(x)) /\ exists(x, Q(x))),
    exists(y, forall(x, R(x)(y))) ==> forall(x, exists(y, R(x)(y))),
    forall(x, Q(x)) ==> exists(x, Q(x)),
    (forall(x, P(x) ==> Q(x)) /\ exists(x, P(x))) ==> exists(x, Q(x)),
    ((a ==> exists(x, Q(x))) /\ a) ==> exists(x, Q(x)),
    forall(x, P(x) ==> Q(f(x))) /\ forall(x, Q(x) ==> R(g(x))(x)) ==> (P(y) ==> R(g(f(y)))(f(y))),
    forall(x, forall(y, P(x) ==> Q(y))) ==> (exists(x, P(x)) ==> forall(y, Q(y))),
    (exists(x, P(x)) ==> forall(y, Q(y))) ==> forall(x, forall(y, P(x) ==> Q(y))),
    forall(x, forall(y, P(x) ==> Q(y))) <=> (exists(x, P(x)) ==> forall(y, Q(y))),
    exists(x, exists(y, P(x) /\ R(x)(y))) ==> (exists(x, P(x) /\ exists(y, R(x)(y)))),
    (exists(x, P(x) /\ exists(y, R(x)(y)))) ==> exists(x, exists(y, P(x) /\ R(x)(y))),
    exists(x, exists(y, P(x) /\ R(x)(y))) <=> (exists(x, P(x) /\ exists(y, R(x)(y)))),
    exists(y, forall(x, P(x) ==> R(x)(y))) ==> (forall(x, P(x)) ==> exists(y, R(x)(y))),
    forall(x, P(x)) ==> P(y),
    !forall(x, D(x) /\ !D(f(x))),
    !forall(x, (D(x) /\ !D(f(x))) \/ (D(x) /\ !D(x))),
    forall(x, forall(y, (E(x)(y) ==> E(f(x))(f(y))) /\ E(f(g(x)))(g(f(x))))) ==> E(f(f(g(u))))(f(g(f(u)))),
    !(forall(x, !((E(f(x))(x)))) /\ forall(x, forall(y, !(E(x)(y)) /\ E(f(x))(g(x))))),
    a1 /\ a2 /\ a3 ==> E(f(f(g(u))))(f(g(f(u)))),
    a1 /\ a2 /\ a3 ==> E(f(g(f(u))))(g(f(f(u)))),
    biga ==> E(f(f(g(u))))(f(g(f(u)))),
    biga ==> E(f(g(f(u))))(g(f(f(u))))
  ).zipWithIndex.map(f =>
    val res = solve(() |- f._1)
    (f._2, f._1, res.nonEmpty, res, res.map(checkSCProof))
  )
   */

}
