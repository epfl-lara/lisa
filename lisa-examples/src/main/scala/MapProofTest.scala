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

import MapProofDef.{*, given}

/**
 * A set of proofs from a functional programming exam about equivalence between
 * `map` and a tail-recursive version of it, `mapTr`.
 *
 * An example of really domain specific proofs using infix extensions.
 */
object MapProofTest extends lisa.Main {

  // available rules
  val MapNil = Nil.map(f) === Nil
  val MapCons = forall(x, forall(xs, (x :: xs).map(f) === (app(f, x) :: xs.map(f))))
  val MapTrNil = forall(xs, Nil.mapTr(f, xs) === xs)
  val MapTrCons = forall(x, forall(xs, forall(ys, (x :: xs).mapTr(f, ys) === xs.mapTr(f, ys ++ (app(f, x) :: Nil)))))
  val NilAppend = forall(xs, (Nil ++ xs) === xs)
  val ConsAppend = forall(x, forall(xs, forall(ys, ((x :: xs) ++ ys) === (x :: (xs ++ ys)))))

  val AccOutNil = Theorem(
    Nil.mapTr(f, (x :: xs)) === (x :: Nil.mapTr(f, xs))
  ) {
    have    ( Nil.mapTr(f, (x :: xs)) === (x :: xs) ) by
          Auto.a(mapTr.NilCase of (xs -> (x :: xs)))
    thenHave( Nil.mapTr(f, (x :: xs)) === (x :: Nil.mapTr(f, xs)) ) by
          Auto(mapTr.NilCase)
  }

  // induction hypothesis
  val IH1 = forall(y, forall(ys, xs.mapTr(f, y :: ys) === (y :: xs.mapTr(f, ys))))
/*
  val AccOutCons = Theorem(
    IH1 |- (x :: xs).mapTr(f, y :: ys) === (y :: (x :: xs).mapTr(f, ys))
  ) {

    assume(mapRules)
    assume(IH1)

    // apply MapTrCons
    have(MapTrCons) by Restate
    val appYYs = thenHave((x :: xs).mapTr(f, (y :: ys)) === xs.mapTr(f, (y :: ys) ++ (app(f, x) :: Nil))) by InstantiateForall(x, xs, (y :: ys))

    // apply ConsAppend
    have(ConsAppend) by Restate
    thenHave((y :: ys) ++ (app(f, x) :: Nil) === (y :: (ys ++ (app(f, x) :: Nil)))) by InstantiateForall(y, ys, (app(f, x) :: Nil))

    val consYYs = have((x :: xs).mapTr(f, (y :: ys)) === xs.mapTr(f, (y :: (ys +++ (app(f, x) :: Nil))))) by Substitution.apply2(false, lastStep)(appYYs)

    // apply IH1
    have(IH1) by Restate
    thenHave(xs.mapTr(f, (y :: (ys +++ (app(f, x) :: Nil)))) === (y :: xs.mapTr(f, (ys +++ (app(f, x) :: Nil))))) by InstantiateForall(y, (ys +++ (app(f, x) :: Nil)))

    val consYXs = have((x :: xs).mapTr(f, (y :: ys)) === (y :: xs.mapTr(f, (ys +++ (app(f, x) :: Nil))))) by Substitution.apply2(false, lastStep)(consYYs)

    // apply mapTr.ConsCase again
    have(mapTr.ConsCase) by Restate
    thenHave((x :: xs).mapTr(f, ys) === xs.mapTr(f, (ys +++ (app(f, x) :: Nil)))) by InstantiateForall(x, xs, ys)

    have(thesis) by Substitution.apply2(true, lastStep)(consYXs)
  }
  show

  val MapEqMapTrNil = Theorem(
    mapRules |- Nil.map(f) === Nil.mapTr(f, Nil)
  ) {
    assume(mapRules)

    // apply MapTrNil
    val trNil = have(Nil.mapTr(f, Nil) === Nil) by InstantiateForall

    // apply map.NilCase
    have(map.NilCase) by Restate
    have(thesis) by Substitution.apply2(true, trNil)(lastStep)
  }
  show

  // the result of induction on the cases above
  val AccOut = forall(xs, IH1)

  // second induction hypothesis
  val IH2 = xs.map(f) === xs.mapTr(f, Nil)

  val MapEqMapCons = Theorem(
    (mapRules :+ IH2 :+ AccOut) |- (x :: xs).map(f) === (x :: xs).mapTr(f, Nil)
  ) {
    assume(mapRules)
    assume(IH2)
    assume(AccOut)

    // apply map.ConsCase
    have(map.ConsCase)
    val mCons = thenHave((x :: xs).map(f) === (app(f, x) :: xs.map(f))) by InstantiateForall(x, xs)

    // apply IH2
    have(IH2) by Restate
    val consTr = have((x :: xs).map(f) === (app(f, x) :: xs.mapTr(f, Nil))) by Substitution.apply2(false, lastStep)(mCons)

    // apply AccOut
    have(IH1) by InstantiateForall
    thenHave(xs.mapTr(f, (app(f, x) :: Nil)) === (app(f, x) :: xs.mapTr(f, Nil))) by InstantiateForall(app(f, x), Nil)
    val trCons = have((x :: xs).map(f) === xs.mapTr(f, (app(f, x) :: Nil))) by Substitution.apply2(true, lastStep)(consTr)

    // apply append.NilCase
    have((Nil +++ (app(f, x) :: Nil)) === (app(f, x) :: Nil)) by InstantiateForall
    val trApp = have((x :: xs).map(f) === xs.mapTr(f, (Nil +++ (app(f, x) :: Nil)))) by Substitution.apply2(true, lastStep)(trCons)

    // apply mapTr.ConsCase
    have(mapTr.ConsCase)
    thenHave((x :: xs).mapTr(f, Nil) === xs.mapTr(f, (Nil +++ (app(f, x) :: Nil)))) by InstantiateForall(x, xs, Nil)

    have(thesis) by Substitution.apply2(true, lastStep)(trApp)
  }
  show

 */
}
