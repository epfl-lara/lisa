package lisa.automation

object TableauTest {
  import lisa.settheory.SetTheoryLibrary.{given, _}
  import lisa.prooflib.Exports.*
  import lisa.prooflib.Substitution.*
  import lisa.utils.K.SCProofChecker.checkSCProof
  import lisa.utils.parsing.FOLPrinter.{prettyTerm, prettyFormula, prettySCProof}
  import Tableau._

  val w = variable
  val x = variable
  val y = variable
  val z = variable

  val a = formulaVariable
  val b = formulaVariable
  val c = formulaVariable
  val d = formulaVariable
  val e = formulaVariable

  val f = function[1]
  val g = function[1]
  val h = function[2]

  val P = predicate[1]
  val Q = predicate[1]
  val R = predicate[2]

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
  println(s"Propositional Positive cases (${posi.size})")
  if posi.exists(f => !f._3) then posi.foreach((i, f, b, proof, judg) => println(s"$i $b" + (if !b then s" $f" else "")))
  else println("All TRUE")
  if posi.exists(tup => tup._5.nonEmpty & !tup._5.get.isValid) then
    println("A proof is wrong")
    posi.foreach(tup =>
      if tup._5.nonEmpty & !tup._5.get.isValid then
        println(prettySCProof(tup._5.get))
        println("\n")
    )
  else println("ALL PROOFS VALID")

  // Quantifier Free

  val posqf = List(
    posi.map(fo => fo._2.substitute(a := P(h(x, y)), b := P(x), c := R(x, h(x, y)))),
    posi.map(fo => fo._2.substitute(a := P(h(x, y)), b := P(h(x, y)), c := R(x, h(x, f(x))))),
    posi.map(fo => fo._2.substitute(a := R(y, y), b := P(h(y, y)), c := R(h(x, y), h(z, y))))
  ).flatten.zipWithIndex.map(f =>
    val res = solve(() |- f._1)
    (f._2, f._1, res.nonEmpty, res, res.map(checkSCProof))
  )
  println(s"First Order Quantifier Free Positive cases (${posqf.size})")
  if posqf.exists(f => !f._3) then posqf.foreach((i, f, b, proof, judg) => println(s"$i $b" + (if !b then s" $f" else "")))
  else println("All TRUE")
  if posqf.exists(tup => tup._5.nonEmpty & !tup._5.get.isValid) then
    println("A proof is wrong")
    posqf.foreach(tup =>
      if tup._5.nonEmpty & !tup._5.get.isValid then
        println(prettySCProof(tup._5.get))
        println("\n")
    )
  else println("ALL PROOFS VALID")

  // First Order Easy

  val poseasy = List(
    posi.map(fo => fo._2.substitute(a := forall(x, P(x)), b := forall(x, P(y)), c := exists(x, P(x)))),
    posi.map(fo => fo._2.substitute(a := forall(x, P(x) /\ Q(f(x))), b := forall(x, P(x) \/ R(y, x)), c := exists(x, Q(x) ==> R(x, y)))),
    posi.map(fo => fo._2.substitute(a := exists(y, forall(x, P(x) /\ Q(f(y)))), b := forall(y, exists(x, P(x) \/ R(y, x))), c := forall(y, exists(x, Q(x) ==> R(x, y)))))
  ).flatten.zipWithIndex.map(f =>
    val res = solve(() |- f._1)
    (f._2, f._1, res.nonEmpty, res, res.map(checkSCProof))
  )
  println(s"First Order Easy Positive cases (${poseasy.size})")
  if poseasy.exists(f => !f._3) then poseasy.foreach((i, f, b, proof, judg) => println(s"$i $b" + (if !b then s" $f" else "")))
  else println("All TRUE")
  if poseasy.exists(tup => tup._5.nonEmpty & !tup._5.get.isValid) then
    println("A proof is wrong")
    poseasy.foreach(tup =>
      if tup._5.nonEmpty & !tup._5.get.isValid then
        println(prettySCProof(tup._5.get))
        println("\n")
    )
  else println("ALL PROOFS VALID")

  // First Order Hard, from https://isabelle.in.tum.de/library/FOL/FOL-ex/Quantifiers_Cla.html

  val poshard = List(
    forall(x, P(x) ==> Q(x)) ==> (forall(x, P(x)) ==> forall(x, Q(x))),
    forall(x, forall(y, R(x, y))) ==> forall(y, forall(x, R(x, y))),
    forall(x, forall(y, R(x, y))) ==> forall(y, forall(x, R(y, x))),
    exists(x, exists(y, R(x, y))) ==> exists(y, exists(x, R(x, y))),
    exists(x, exists(y, R(x, y))) ==> exists(y, exists(x, R(y, x))),
    (forall(x, P(x)) \/ forall(x, Q(x))) ==> forall(x, P(x) \/ Q(x)),
    forall(x, a ==> Q(x)) <=> (a ==> forall(x, Q(x))),
    forall(x, P(x) ==> a) <=> (exists(x, P(x)) ==> a),
    exists(x, P(x) \/ Q(x)) <=> (exists(x, P(x)) \/ exists(x, Q(x))),
    exists(x, P(x) /\ Q(x)) ==> (exists(x, P(x)) /\ exists(x, Q(x))),
    exists(y, forall(x, R(x, y))) ==> forall(x, exists(y, R(x, y))),
    forall(x, Q(x)) ==> exists(x, Q(x)),
    (forall(x, P(x) ==> Q(x)) /\ exists(x, P(x))) ==> exists(x, Q(x)),
    ((a ==> exists(x, Q(x))) /\ a) ==> exists(x, Q(x)),
    forall(x, P(x) ==> Q(f(x))) /\ forall(x, Q(x) ==> R(g(x), x)) ==> (P(y) ==> R(g(f(y)), f(y))),
    forall(x, forall(y, P(x) ==> Q(y))) ==> (exists(x, P(x)) ==> forall(y, Q(y))),
    (exists(x, P(x)) ==> forall(y, Q(y))) ==> forall(x, forall(y, P(x) ==> Q(y))),
    forall(x, forall(y, P(x) ==> Q(y))) <=> (exists(x, P(x)) ==> forall(y, Q(y))),
    exists(x, exists(y, P(x) /\ R(x, y))) ==> (exists(x, P(x) /\ exists(y, R(x, y)))),
    (exists(x, P(x) /\ exists(y, R(x, y)))) ==> exists(x, exists(y, P(x) /\ R(x, y))),
    exists(x, exists(y, P(x) /\ R(x, y))) <=> (exists(x, P(x) /\ exists(y, R(x, y)))),
    exists(y, forall(x, P(x) ==> R(x, y))) ==> (forall(x, P(x)) ==> exists(y, R(x, y))),
    forall(x, P(x)) ==> P(y)
  ).zipWithIndex.map(f =>
    val res = solve(() |- f._1)
    (f._2, f._1, res.nonEmpty, res, res.map(checkSCProof))
  )
  println(s"First Order Hard Positive cases (${poshard.size})")
  if poshard.exists(f => !f._3) then poshard.foreach((i, f, b, proof, judg) => println(s"$i $b" + (if !b then s" $f" else "")))
  else println("All TRUE")
  if poshard.exists(tup => tup._5.nonEmpty & !tup._5.get.isValid) then
    println("A proof is wrong")
    poshard.foreach(tup =>
      if tup._5.nonEmpty & !tup._5.get.isValid then
        println(prettySCProof(tup._5.get))
        println("\n")
    )
  else println("ALL PROOFS VALID")
}
