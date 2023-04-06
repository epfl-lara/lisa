import lisa.automation.kernel.OLPropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProofChecker.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.mathematics.SetTheory.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.*
import lisa.utils.FOLPrinter.*
import lisa.utils.KernelHelpers.checkProof
import lisa.utils.parsing.FOLPrinter
import lisa.utils.unification.UnificationUtils.*

/**
 * A set of proofs from a functional programming exam about equivalence between
 * `map` and a tail-recursive version of it, `mapTr`.
 *
 * An example of really domain specific proofs using infix extensions.
 */
object MapProofTest extends lisa.Main {
  val Nil = variable
  val Cons = function(2)
  val append = function(2)
  val x = variable
  val y = variable
  val xs = variable
  val ys = variable
  val f = variable

  val map_ = function(2)
  val mapTr_ = function(3)

  // some more DSL
  extension (t1: Term) {
    infix def ::(t2: Term) = Cons(t1, t2)
    infix def ++(t2: Term) = append(t1, t2)
    def map(t2: Term) = map_(t1, t2)
    def mapTr(t2: Term, t3: Term) = mapTr_(t1, t2, t3)
  }

  // available rules
  val MapNil = Nil.map(f) === Nil
  val MapCons = forall(x, forall(xs, (x :: xs).map(f) === (app(f, x) :: xs.map(f))))
  val MapTrNil = forall(xs, Nil.mapTr(f, xs) === xs)
  val MapTrCons = forall(x, forall(xs, forall(ys, (x :: xs).mapTr(f, ys) === xs.mapTr(f, ys ++ (app(f, x) :: Nil)))))
  val NilAppend = forall(xs, (Nil ++ xs) === xs)
  val ConsAppend = forall(x, forall(xs, forall(ys, ((x :: xs) ++ ys) === Cons(x, append(xs, ys)))))

  val mapRules = Seq(
    MapNil,
    MapCons,
    MapTrNil,
    MapTrCons,
    NilAppend,
    ConsAppend
  )

  val AccOutNil = Theorem(
    mapRules |- Nil.mapTr(f, (x :: xs)) === (x :: Nil.mapTr(f, xs))
  ) {
    assume(mapRules)

    // apply MapTrNil
    have(Nil.mapTr(f, (x :: xs)) === (x :: xs)) by InstantiateForall

    // apply MapTrNil again
    thenHave(Nil.mapTr(f, xs) === xs |- Nil.mapTr(f, (x :: xs)) === (x :: Nil.mapTr(f, xs))) by Substitution.applyRule(flip = true, Nil.mapTr(f, xs) === xs)
    thenHave(thesis) by LeftForall
  }
  show

  // induction hypothesis
  val IH1 = forall(y, forall(ys, xs.mapTr(f, y :: ys) === (y :: xs.mapTr(f, ys))))

  val AccOutCons = Theorem(
    (mapRules :+ IH1) |- (x :: xs).mapTr(f, y :: ys) === (y :: (x :: xs).mapTr(f, ys))
  ) {
    assume(mapRules)
    assume(IH1)

    // apply MapTrCons
    have(MapTrCons) by Restate
    val appYYs = thenHave((x :: xs).mapTr(f, (y :: ys)) === xs.mapTr(f, append((y :: ys), (app(f, x) :: Nil)))) by InstantiateForall(x, xs, (y :: ys))

    // apply ConsAppend
    have(ConsAppend) by Restate
    thenHave(append((y :: ys), (app(f, x) :: Nil)) === (y :: (ys ++ (app(f, x) :: Nil)))) by InstantiateForall(y, ys, (app(f, x) :: Nil))

    val consYYs = have((x :: xs).mapTr(f, (y :: ys)) === xs.mapTr(f, (y :: (ys ++ (app(f, x) :: Nil))))) by Substitution.applyRule(flip = false, lastStep)(appYYs)

    // apply IH1
    have(IH1) by Restate
    thenHave(xs.mapTr(f, (y :: (ys ++ (app(f, x) :: Nil)))) === (y :: xs.mapTr(f, (ys ++ (app(f, x) :: Nil))))) by InstantiateForall(y, (ys ++ (app(f, x) :: Nil)))

    val consYXs = have((x :: xs).mapTr(f, (y :: ys)) === (y :: xs.mapTr(f, (ys ++ (app(f, x) :: Nil))))) by Substitution.applyRule(flip = false, lastStep)(consYYs)

    // apply MapTrCons again
    have(MapTrCons) by Restate
    thenHave((x :: xs).mapTr(f, ys) === xs.mapTr(f, (ys ++ (app(f, x) :: Nil)))) by InstantiateForall(x, xs, ys)

    have(thesis) by Substitution.applyRule(flip = true, lastStep)(consYXs)
  }
  show

  val MapEqMapTrNil = Theorem(
    mapRules |- Nil.map(f) === Nil.mapTr(f, Nil)
  ) {
    assume(mapRules)

    // apply MapTrNil
    val trNil = have(Nil.mapTr(f, Nil) === Nil) by InstantiateForall

    // apply MapNil
    have(MapNil) by Restate
    have(thesis) by Substitution.applyRule(flip = true, trNil)(lastStep)
  }
  show

  // the result of induction on the cases above
  val AccOut = forall(xs, IH1)

  // second induction hypothesis
  val IH2 = xs.map(f) === xs.mapTr(f, Nil)

  val MapEqMapTrCons = Theorem(
    (mapRules :+ IH2 :+ AccOut) |- (x :: xs).map(f) === (x :: xs).mapTr(f, Nil)
  ) {
    assume(mapRules)
    assume(IH2)
    assume(AccOut)

    // apply MapCons
    have(MapCons) by Restate
    val mCons = thenHave((x :: xs).map(f) === (app(f, x) :: xs.map(f))) by InstantiateForall(x, xs)

    // apply IH2
    have(IH2) by Restate
    val consTr = have((x :: xs).map(f) === (app(f, x) :: xs.mapTr(f, Nil))) by Substitution.applyRule(flip = false, lastStep)(mCons)

    // apply AccOut
    have(IH1) by InstantiateForall
    thenHave(xs.mapTr(f, (app(f, x) :: Nil)) === (app(f, x) :: xs.mapTr(f, Nil))) by InstantiateForall(app(f, x), Nil)
    val trCons = have((x :: xs).map(f) === xs.mapTr(f, (app(f, x) :: Nil))) by Substitution.applyRule(flip = true, lastStep)(consTr)

    // apply NilAppend
    have((Nil ++ (app(f, x) :: Nil)) === (app(f, x) :: Nil)) by InstantiateForall
    val trApp = have((x :: xs).map(f) === xs.mapTr(f, (Nil ++ (app(f, x) :: Nil)))) by Substitution.applyRule(flip = true, lastStep)(trCons)

    // apply MapTrCons
    have(MapTrCons) by Restate
    thenHave((x :: xs).mapTr(f, Nil) === xs.mapTr(f, (Nil ++ (app(f, x) :: Nil)))) by InstantiateForall(x, xs, Nil)

    have(thesis) by Substitution.applyRule(flip = true, lastStep)(trApp)
  }
  show
}
