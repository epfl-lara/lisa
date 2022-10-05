package lisa.utilities.prooftransform
import lisa.kernel.proof.SCProof
import lisa.utils.Helpers.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.fol.FOL.*
import lisa.utils.Printer

case class ProofUnconditionalizer (prOrig : SCProof) extends ProofTransformer(prOrig) {

    //ATTRIBUTES#########################################################################################################################
    private val pr = ProofInstantiationRemover(prOrig).transform()
    private val neg_premises = dependency_finder(pr.steps, ps => ps.premises.filter(_>=0).map(pr.steps(_)), ps => ps.premises)
    //We use a var because Subproofs require the results of precedent steps, topological order on proofs ensure we can always do this
    private var appended_steps = IndexedSeq[SCProofStep]()    
    //PREDICATES#########################################################################################################################
    /**
      * Wether a step needs to be more modified than just appending hypothesis on the left of the conclusion
      *
      * @param sc the step to analyse
      * @return whether the step has a negative premise
      */ 
    private def is_problematic(sc : SCProofStep): Boolean = sc.premises.exists(_ < 0)

    //PUBLIC FUNCTIONS###################################################################################################################
    /**
      * Maps a proof to a new proof where all imports are made into suppositions on the left of the conclusion
      *
      * @return A proof where each steps has the necessary imports added as suppostitions on the left of their bottom
      */
    def transform() : SCProof = transformPrivate(IndexedSeq.empty)

    //PRIVATE FUNCTIONS##################################################################################################################
    /**
      * Private version used to keep track of imports that should not be removed, useful for SubProofs
      *
      * @param keep The indices not to be removed from the transformed proof
      * @return a proof zhose imports have been removed except for those present in keep
      */
    private def transformPrivate( keep : IndexedSeq[Sequent])  : SCProof = {
        pr.steps.zipWithIndex.foreach((pS, i) => {
            appended_steps = appended_steps.appended( 
            if(is_problematic(pS)) {
                mapProb(pS)
            } else {
                mapStep(pS, b => neg_premises.getOrElse(pS, Set[Int]()).map(i => sequentToFormula(pr.imports(-i-1))) ++ b )
            })
        })
        SCProof(appended_steps.toIndexedSeq, keep)
    }
    
    /**
      * Deals with steps that have a negative premise
      * The strategy is to systematically add an hypothesis to introduce the import, rewrite it
      * to remove unwanted clutter and apply strictly the same transformation as if there was no negative premise.
      * To not mess with indices of proof and to keep a clearer proof structure all those steps are wrapped into a SubProof
      *
      * @param pS thestep to be modified
      * @return a subproof whose conclusion is the same step as in the argument but with changed premises and a left side bottom modified as
      * in the general algorithm
      */
    private def mapProb(pS : SCProofStep) = {
        val premises = pS.premises.filter(_ < 0)
                .map(i => pr.imports(-i-1))
        val hypothesis = premises
                .map((se) => {
                val h = Hypothesis((se.left + sequentToFormula(se)) |- (se.right + sequentToFormula(se)), sequentToFormula(se))
                h
                })
        val rewrites = hypothesis.zipWithIndex.map((h, i) => {
                    val r = Rewrite(h.bot.left |- (h.bot.right - sequentToFormula(premises(i))), i)
                    r
                })
        //We must separate the case for subproofs for they need to use the modified version of the precedent 
        val inner = pS match {
            case SCSubproof(_,_,_) => SCProof(hypothesis.toIndexedSeq ++ rewrites.toIndexedSeq ++ IndexedSeq(
                    mapStep(pS, b => neg_premises(pS).map(i => sequentToFormula(pr.imports(-i-1))) ++ b, s => s.map(i => i match {
                        case i if i < 0 => -i-2 + hypothesis.length
                        case i => -i
                    } ), rewrites.map(_.bot))) , pS.premises.filter(_>= 0).map(appended_steps(_).bot).toIndexedSeq)
            
            case _ => SCProof(hypothesis.toIndexedSeq ++ IndexedSeq(
                    mapStep(pS, b => neg_premises(pS).map(i => sequentToFormula(pr.imports(-i-1))) ++ b, premise => premise.zipWithIndex.map((i,j) => i match {
                        case i if i < 0 => j
                        case i => -j
                    } ))) , pS.premises.filter(_>= 0).map(appended_steps(_).bot).toIndexedSeq)   
        }
        SCSubproof(inner, pS.premises.filter(_ >= 0))
    }
    /**
      * This function transform generically a proof step into another one
      *
      * @param pS the proofstep to modify
      * @param f the transformation on left side of bottom
      * @param fi transformation on premises
      * @param fsub sequents to keep on subproofs
      * @return a proofstep where each function is applied to the corresponding 
      */
    protected def mapStep(pS : SCProofStep, f : Set[Formula] => Set[Formula], fi : Seq[Int] => Seq[Int] = identity, fsub : Seq[Sequent] = Nil) : SCProofStep= pS match
    {
            case Rewrite(bot, t1)                           => Rewrite(f(bot.left)|- bot.right, fi(pS.premises).head)
            case Hypothesis(bot, phi)                       => Hypothesis(f(bot.left)|- bot.right, phi)
            case Cut(bot, t1, t2, phi)                      => Cut(f(bot.left)|- bot.right, fi(pS.premises).head, fi(pS.premises).last, phi)
            case LeftAnd(bot, t1, phi, psi)                 => LeftAnd(f(bot.left)|- bot.right, fi(pS.premises).head, phi, psi)
            case LeftOr(bot, t, disjuncts)                  => LeftOr(f(bot.left)|- bot.right, fi(t), disjuncts)
            case LeftImplies(bot, t1, t2, phi, psi)         => LeftImplies(f(bot.left)|- bot.right, fi(pS.premises).head, t2, phi, psi)
            case LeftIff(bot, t1, phi, psi)                 => LeftIff(f(bot.left)|- bot.right, fi(pS.premises).head, phi, psi)
            case LeftNot(bot, t1, phi)                      => LeftNot(f(bot.left)|- bot.right, fi(pS.premises).head, phi)
            case LeftForall(bot, t1, phi, x, t)             => LeftForall(f(bot.left)|- bot.right, fi(pS.premises).head, phi, x, t)
            case LeftExists(bot, t1, phi, x)                => LeftExists(f(bot.left)|- bot.right, fi(pS.premises).head, phi, x)
            case LeftExistsOne(bot, t1, phi, x)             => LeftExistsOne(f(bot.left)|- bot.right, fi(pS.premises).head, phi, x)
            case RightAnd(bot, t, cunjuncts)                => RightAnd(f(bot.left)|- bot.right, fi(t), cunjuncts)
            case RightOr(bot, t1, phi, psi)                 => RightOr(f(bot.left)|- bot.right, fi(pS.premises).head, phi, psi)
            case RightImplies(bot, t1, phi, psi)            => RightImplies(f(bot.left)|- bot.right, fi(pS.premises).head, phi, psi)
            case RightIff(bot, t1, t2, phi, psi)            => RightIff(f(bot.left)|- bot.right, fi(pS.premises).head, fi(pS.premises).last, phi, psi)
            case RightNot(bot, t1, phi)                     => RightNot(f(bot.left)|- bot.right, fi(pS.premises).head, phi)
            case RightForall(bot, t1, phi, x)               => RightForall(f(bot.left)|- bot.right, fi(pS.premises).head, phi, x)
            case RightExists(bot, t1, phi, x, t)            => RightExists(f(bot.left)|- bot.right, fi(pS.premises).head, phi, x, t)
            case RightExistsOne(bot, t1, phi, x)            => RightExistsOne(f(bot.left)|- bot.right, fi(pS.premises).head, phi, x)
            case Weakening(bot, t1)                         => Weakening(f(bot.left)|- bot.right, fi(pS.premises).head)
            case LeftRefl(bot, t1, fa)                      => LeftRefl(f(bot.left)|- bot.right, fi(pS.premises).head, fa)
            case RightRefl(bot, fa)                         => RightRefl(f(bot.left)|- bot.right, fa)
            case LeftSubstEq(bot, t1, equals, lambdaPhi)    => LeftSubstEq(f(bot.left) |- bot.right, fi(pS.premises).head, equals, lambdaPhi)
            case RightSubstEq(bot,  t1, equals, lambdaPhi)  => RightSubstEq(f(bot.left)|- bot.right, fi(pS.premises).head, equals, lambdaPhi)
            case LeftSubstIff(bot, t1, equals, lambdaPhi)   => LeftSubstIff(f(bot.left) |- bot.right, fi(pS.premises).head, equals, lambdaPhi)
            case RightSubstIff(bot, t1, equals, lambdaPhi)  => RightSubstIff(f(bot.left)|- bot.right, fi(pS.premises).head, equals, lambdaPhi)
            case InstFunSchema(bot, t1, insts)              => InstFunSchema(instantiateFunctionSchemaInSequent(f(bot.left)|- bot.right, insts).left |- bot.right, fi(pS.premises).head, insts)
            case InstPredSchema(bot, t1, insts)             => InstPredSchema(instantiatePredicateSchemaInSequent(f(bot.left) |- bot.right,insts).left |- bot.right, fi(pS.premises).head, insts)
            case SCSubproof(pp, t, b)                       => {
                SCSubproof(ProofUnconditionalizer(pp).transformPrivate(fsub.toIndexedSeq ++ t.filter(_ >= 0).map(i => appended_steps(i).bot).toIndexedSeq), fi(t), b)}
    }
  
}
