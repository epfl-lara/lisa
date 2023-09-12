import lisa.automation.kernel.OLPropositionalSolver.*
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProofChecker.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.mathematics.settheory.SetTheory.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.*
import lisa.prooflib.Substitution.ApplyRules
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
  /*
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
  val ConsAppend = forall(x, forall(xs, forall(ys, ((x :: xs) ++ ys) === (x :: (xs ++ ys)))))

  val AccOutNil = Theorem(
    MapTrNil |- Nil.mapTr(f, (x :: xs)) === (x :: Nil.mapTr(f, xs))
  ) {
    assume(MapTrNil)

    // apply MapTrNil
    have(Nil.mapTr(f, (x :: xs)) === (x :: xs)) by InstantiateForall

    // apply MapTrNil again
    thenHave(Nil.mapTr(f, xs) === xs |- Nil.mapTr(f, (x :: xs)) === (x :: Nil.mapTr(f, xs))) by ApplyRules(Nil.mapTr(f, xs) === xs)
    thenHave(thesis) by LeftForall
  }
  show

  // induction hypothesis
  val IH1 = forall(y, forall(ys, xs.mapTr(f, y :: ys) === (y :: xs.mapTr(f, ys))))

  val AccOutCons = Theorem(
    (MapTrCons, ConsAppend, IH1) |- (x :: xs).mapTr(f, y :: ys) === (y :: (x :: xs).mapTr(f, ys))
  ) {
    assume(MapTrCons)
    assume(ConsAppend)
    assume(IH1)

    // apply MapTrCons
    have(MapTrCons) by Restate
    val appYYs = thenHave((x :: xs).mapTr(f, (y :: ys)) === xs.mapTr(f, (y :: ys) ++ (app(f, x) :: Nil))) by InstantiateForall(x, xs, (y :: ys))

    // apply ConsAppend
    have(ConsAppend) by Restate
    thenHave((y :: ys) ++ (app(f, x) :: Nil) === (y :: (ys ++ (app(f, x) :: Nil)))) by InstantiateForall(y, ys, (app(f, x) :: Nil))

    val consYYs = have((x :: xs).mapTr(f, (y :: ys)) === xs.mapTr(f, (y :: (ys ++ (app(f, x) :: Nil))))) by ApplyRules(lastStep)(appYYs)

    // apply IH1
    have(IH1) by Restate
    thenHave(xs.mapTr(f, (y :: (ys ++ (app(f, x) :: Nil)))) === (y :: xs.mapTr(f, (ys ++ (app(f, x) :: Nil))))) by InstantiateForall(y, (ys ++ (app(f, x) :: Nil)))

    val consYXs = have((x :: xs).mapTr(f, (y :: ys)) === (y :: xs.mapTr(f, (ys ++ (app(f, x) :: Nil))))) by ApplyRules(lastStep)(consYYs)

    // apply MapTrCons again
    have(MapTrCons) by Restate
    thenHave((x :: xs).mapTr(f, ys) === xs.mapTr(f, (ys ++ (app(f, x) :: Nil)))) by InstantiateForall(x, xs, ys)

    have(thesis) by ApplyRules(lastStep)(consYXs)
  }
  show

  val MapEqMapTrNil = Theorem(
    (MapNil, MapTrNil) |- Nil.map(f) === Nil.mapTr(f, Nil)
  ) {
    assume(MapNil)
    assume(MapTrNil)

    // apply MapTrNil
    val trNil = have(Nil.mapTr(f, Nil) === Nil) by InstantiateForall

    // apply MapNil
    have(MapNil) by Restate
    have(thesis) by ApplyRules(trNil)(lastStep)
  }
  show

  // second induction hypothesis
  val IH2 = xs.map(f) === xs.mapTr(f, Nil)

  val MapEqMapTrCons = Theorem(
    (MapCons, IH2, NilAppend, MapTrCons, ConsAppend, IH1) |- (x :: xs).map(f) === (x :: xs).mapTr(f, Nil)
  ) {
    assume(MapCons)
    assume(IH2)
    assume(NilAppend)
    assume(MapTrCons)
    // assumptions from last proof
    assume(ConsAppend)
    assume(IH1)

    // apply MapCons
    have(MapCons) by Restate
    val mCons = thenHave((x :: xs).map(f) === (app(f, x) :: xs.map(f))) by InstantiateForall(x, xs)

    // apply IH2
    have(IH2) by Restate
    val consTr = have((x :: xs).map(f) === (app(f, x) :: xs.mapTr(f, Nil))) by ApplyRules(lastStep)(mCons)

    // apply AccOut TODO: expand this to be inductive
    have(IH1) by Restate
    thenHave(xs.mapTr(f, (app(f, x) :: Nil)) === (app(f, x) :: xs.mapTr(f, Nil))) by InstantiateForall(app(f, x), Nil)
    val trCons = have((x :: xs).map(f) === xs.mapTr(f, (app(f, x) :: Nil))) by ApplyRules(lastStep)(consTr)

    // apply NilAppend
    have((Nil ++ (app(f, x) :: Nil)) === (app(f, x) :: Nil)) by InstantiateForall
    val trApp = have((x :: xs).map(f) === xs.mapTr(f, (Nil ++ (app(f, x) :: Nil)))) by ApplyRules(lastStep)(trCons)

    // apply MapTrCons
    have(MapTrCons) by Restate
    thenHave((x :: xs).mapTr(f, Nil) === xs.mapTr(f, (Nil ++ (app(f, x) :: Nil)))) by InstantiateForall(x, xs, Nil)

    have(thesis) by ApplyRules(lastStep)(trApp)
  }
  show*/
}
