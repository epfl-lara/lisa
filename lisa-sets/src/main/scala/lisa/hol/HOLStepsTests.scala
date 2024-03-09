package lisa.hol
import lisa.hol.HOLSteps.*
import lisa.prooflib.BasicStepTactic.* 
import lisa.prooflib.SimpleDeducedSteps.Restate
import java.beans.Beans

object HOLStepsTests extends lisa.HOL {
  


  // REFL


  // _TRANS

/*
  val test_trans_1 = Theorem((w =:= x, x =:= y, y =:= z) |- (w =:=z)) {
    val a1 = assume(w =:= x)
    val a2 = assume(x =:= y)
    val a3 = assume(y =:= z)
    val s1 = have(_TRANS(a1, a2))
    have(_TRANS(s1, a3))
  }
  println("Starting tests")
  val now = System.currentTimeMillis()

  // MK_Comb

  val test_mkcomb_1 = Theorem((f =:= g, x =:= y) |- (f*x =:= g*y)) {
    val a1 = assume(f =:= g)
    val a2 = assume(x =:= y)
    have(MK_COMB(a1, a2))
  }

  // ABS

  val test_abs_1 = Theorem((y =:= z) |- (λ(x, y) =:= λ(x, z))) {
    assume(y =:= z)
    have(ABS(x)(lastStep))
  }

  val thm_abs_2 = Theorem(λ(x, λ(y, y)) =:= λ(x, λ(z, z))) {
    have(λ(y, y) =:= λ(z, z)) by Sorry
    have(ABS(x)(lastStep))
  }

  val thm_abs_3 = Theorem(λ(x, λ(y, x)) =:= λ(x, λ(z, x))) {
    have(λ(y, x) =:= λ(z, x)) by Sorry
    have(ABS(x)(lastStep))
  }

  val test_abs_4 = Theorem(λ(x, λ(y, f*x =:= g*(λ(z, y)*x))) =:= λ(x, λ(z, z =:= x))) {
    have(λ(y, f*x =:= g*(λ(z, y)*x)) =:= λ(z, z =:= x)) by Sorry
    have(ABS(x)(lastStep))
  }
  println("starting beta")
  // BETA

  val test_beta_1 = Theorem( λ(x, x)*x =:= x) {
    have(BETA(λ(x, x)*x))
  }

  val test_beta_2 = Theorem( λ(x, x)*x =:= (x)) {
    have(BETA(λ(x, x)*x))
  }

  val test_beta_3 = Theorem( λ(x, y)*x =:= (y)) {
    have(BETA(λ(x, y)*x))
  }

  val test_beta_4 = Theorem( λ(x, x =:= x)*x =:= (x =:= x)) {
    have(BETA(λ(x, x =:= x)*x))
  }

  val test_beta_5 = Theorem( λ(x, x =:= y)*x =:= (x =:= y)) {
    have(BETA(λ(x, x =:= y)*x))
  }

  val test_beta_6 = Theorem( λ(x, λ(y, x))*x =:= λ(y, x)) {
    have(BETA(λ(x, λ(y, x))*x))
  }

  val test_beta_7 = Theorem( λ(x, λ(y, y))*x =:= λ(y, y)) {
    have(BETA(λ(x, λ(y, y))*x))
  }

  val test_beta_8 = Theorem( λ(x, λ(y, x =:= y))*x =:= λ(y, x =:= y)) {
    have(BETA(λ(x, λ(y, x =:= y))*x))
  }


  val test_beta_9 = Theorem( λ(x, λ(y, λ(z, x)))*x =:= λ(y, λ(z, x))) {
    have(BETA(λ(x, λ(y, λ(z, x)))*x))
  }

  val test_beta_10 = Theorem( λ(x, λ(y, λ(z, y) =:= λ(w, x)))*x =:= λ(y, λ(z, y) =:= λ(w, x))) {
    have(BETA(λ(x, λ(y, λ(z, y) =:= λ(w, x)))*x))
  }

  println("starting eta")
  // ETA

  val test_eta_1 = Theorem(λ(x, f*x) =:= f) {
    have(ETA(x, f))
  }
  val test_eta_prim_1 = Theorem(withCTX(λ(x, f*x) === f)) {
    have(ETA_PRIM(x, f))
  }

  val f2 = λ(y, y)
  val test_eta_2 = Theorem(λ(x, f2*x) =:= f2) {
    have(ETA(x, f2))
  }
  val test_eta_prim_2 = Theorem(withCTX(λ(x, f2*x) === f2)) {
    have(ETA_PRIM(x, f2))
  }

  val f3 = λ(y, y =:= z) 
  val test_eta_3 = Theorem(λ(x, f3*x) =:= f3) {
    have(ETA(x, f3))
  }
  val test_eta_prim_3 = Theorem(withCTX(λ(x, f3*x) === f3)) {
    have(ETA_PRIM(x, f3))
  }

  val f4 = λ(y, λ(z, f*y))
  val test_eta_4 = Theorem(λ(x, f4*x) =:= f4) {
    have(ETA(x, f4))
  }
  val test_eta_prim_4 = Theorem(withCTX(λ(x, f4*x) === f4)) {
    have(ETA_PRIM(x, f4))
  }

  val f5 = f2
  val test_eta_5 = Theorem(λ(y, f5*y) =:= f5) {
    have(ETA(y, f5))
  }
  val test_eta_prim_5 = Theorem(withCTX(λ(y, f5*y) === f5)) {
    have(ETA_PRIM(y, f5))
  }


  // ASSUME

  val b = typedvar(𝔹)

  val test_assume_1 = Theorem(b |- b) {
    have(ASSUME(b))
  }

  val test_assume_2 = Theorem((x =:= x) |- (x =:= x)) {
    have(ASSUME(x =:= x))
  }

  val test_assume_3 = Theorem( (λ(x, y) =:= λ(x, y)) |- (λ(x, y) =:= λ(x, y)) ){
    have(ASSUME(λ(x, y) =:= λ(x, y)))
  }

  val expr = λ(f, λ(x, f*x =:= f*(h*v)))*λ(y, f*y)*y
  val test_assume_4 = Theorem( expr  |- expr ){
    have(ASSUME(expr))
  }
  

  val (a1, a2) = (p, q)
  val test_eqmp_1 = Theorem((a1 =:= a2, a1) |- a2) {
    val s1 = assume(p =:= q)
    val s2 = assume(p)
    have(_EQ_MP(s1, s2))
  }

  val (a3, a4) = (λ(x, p) =:= λ(x, p), λ(p, q)*p)
  val test_eqmp_2 = Theorem((a3 =:= a4, a3) |- a4) {
    val s1 = assume(a3 =:= a4)
    val s2 = assume(a3)
    have(_EQ_MP(s1, s2))
  }

  val test_eqmp_3 = Theorem(λ(p, p)*p |- p ) {
    val s1 = have(BETA(λ(p, p)*p))
    val s2 = assume(λ(p, p)*p)
    have(_EQ_MP(s1, s2))
  }

  val test_deductantisymrule_1 = Theorem(withCTX(((p === One) ==> (q === One), (q === One) ==> (p === One)) |- ((p =:= q) === One))){
    assume((p === One) ==> (q === One))
    assume((q === One) ==> (p === One))
    val s1 = have(q |- p) by Restate
    val s2 = have(p |- q) by Restate
    have(DEDUCT_ANTISYM_RULE(s1, s2))
  }
  */
  println("start inst tests")
  /*
  val test_inst_1 = Theorem(q){
    have(p) by Sorry
    have(INST(Seq((p, q)), lastStep))
  }

  println("Starting test 2")
  val test_inst_2 = Theorem(q) {
    have(q) by Sorry
    have(INST(Seq((p, p=:=p)), lastStep))
  }
  println("Starting test 3")
  val test_inst_3 = Theorem(p =:= p){
    have(p =:= q) by Sorry
    have(INST(Seq((q, p)), lastStep))
  }
  */

  /*
  println("Starting test 4")
  val test_inst_4 = Theorem(p =:= q) {
    have(p) by Sorry
    have(INST(Seq((p, p=:=q)), lastStep))
  }*/

  println("Starting test 5")
  val test_inst_5 = Theorem(λ(x, y)*z =:= z){
    have(λ(x, y)*w =:= w) by Sorry
    have(INST(Seq((w, z)), lastStep))
  }


  println("Starting test 6")
  val test_inst_6 = Theorem(λ(x, y)*z =:= y){
    have(BETA(λ(x, y)*x))
    have(INST(Seq((x, z)), lastStep))
  }

  println("Starting test 7")
  val test_inst_7 = Theorem(λ(x, x)*z =:= z){
    have(λ(x, x)*x =:= x) by Sorry
    have(INST(Seq((x, z)), lastStep))
  }

  println("Starting test 8")
  val test_inst_8 = Theorem(λ(x, x =:= y)*z =:= (z =:= y)){
    have(BETA(λ(x, x =:= y)*x))
    have(INST(Seq((x, z)), lastStep))
  }

  


/*
  val test_inst_10 = Theorem(λ(x, λ(x, y)*x)*y =:= y){
    val s1 = have(BETA(λ(x, λ(x, y)*x)*x))
    println("s1: " + s1.statement)
    val s2 = have(INST(Seq((x, y)), s1)) // λ(x, λ(x, y)*x)*y === λ(x, y)*y
    println("s2: " + s2.statement)
    val s3 = have(BETA(λ(x, y)*x)) // λ(x, y)*x =:= y
    println("s3: " + s3.statement)
    val s4 = have(INST(Seq((x, y)), s3)) // λ(x, y)*y =:= y
    println("s4: " + s4.statement)
    have(_TRANS(s2, s4))
  }

  val test_inst_11 = Theorem(λ(x, f*z) =:= λ(x, f*z)){
    val s0 = have(REFL(λ(x, y)))
    val s1 = have(INST(Seq((y, f*z)), s0))
    val s2 = have(REFL(λ(x, f*z) ))
    have(_TRANS(s1, s2))

  }
*/

}
