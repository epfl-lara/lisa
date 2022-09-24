package lisa.transformers

import lisa.kernel.proof.SCProof
import lisa.utils.Helpers.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.fol.FOL.*
import lisa.utils.Printer

class SimpleProofTransformer (pr : SCProof) extends Transformer {

    val (neg_premises) = dependency_finder(pr.steps, ps => ps.premises.filter(_>=0).map(pr.steps(_)), ps => ps.premises)
    var appended_steps = IndexedSeq[SCProofStep]()
    /**
     * 
     * pr : Int => SCProofStep
     * 
     * cache : SCProofStep => [Int]
     * 
     * 
     * 
     **/
    def is_problematic(sc : SCProofStep): Boolean = sc.premises.exists(_ < 0)
    def transform_premises(pS : SCProofStep, b : Set[Formula]) = neg_premises.getOrElse(pS, Set[Int]()).map(i => sequentToFormula(pr.imports(-i-1))) ++ b 
    def transform( keep : IndexedSeq[Sequent] = IndexedSeq.empty)  : SCProof = {
        pr.steps.zipWithIndex.foreach((pS, i) => {
            appended_steps = appended_steps.appended( 
            if(is_problematic(pS)) {
                mapProb(pS)
            } else {
                mapStep(pS, b => transform_premises(pS, b))
            })
        })
        SCProof(appended_steps.toIndexedSeq, keep)
    }
        
    def mapProb(pS : SCProofStep) = pS match {
        case SCSubproof(_,_,_) => {
            val p = pS
            val premises = p.premises.filter(_ < 0)
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
            
            val inner = SCProof(hypothesis.toIndexedSeq ++ rewrites.toIndexedSeq ++ IndexedSeq(
                mapStep(p, b => neg_premises(p).map(i => sequentToFormula(pr.imports(-i-1))) ++ b, s => s.map(i => i match {
                    case i if i < 0 => -i-2 + hypothesis.length
                    case i => -i
                } ), rewrites.map(_.bot))
            ) , p.premises.filter(_>= 0).map(pr(_).bot).toIndexedSeq)
            val res = SCSubproof(inner, p.premises.filter(_ >= 0))
            res
        }
        case p => {
            val premises = p.premises.filter(_ < 0)
                .map(i => pr.imports(-i-1))
            val hypothesis = premises
                .map((se) => {
                val h = Hypothesis((se.left + sequentToFormula(se)) |- (se.right + sequentToFormula(se)), sequentToFormula(se))
                h
                })
            println(neg_premises(p))
            val rewrites  = hypothesis.zipWithIndex.map((h, i) => {
                    val r = Rewrite(h.bot.left |- (h.bot.right - sequentToFormula(premises(i))), i)
                    r
                })
            
            val inner = SCProof(hypothesis.toIndexedSeq ++ rewrites.toIndexedSeq ++ IndexedSeq(
                mapStep(p, b => neg_premises(p).map(i => sequentToFormula(pr.imports(-i-1))) ++ b, s => s.map(i => i match {
                    case i if i < 0 => -i-1 + hypothesis.length
                    case i => -i
                } ))
            ) , p.premises.filter(_>= 0).map(pr(_).bot).toIndexedSeq)
            val res = SCSubproof(inner, p.premises.filter(_ >= 0))
            res
        }
    }
    // a -> b |- !a \/ b
    def mapStep(pS : SCProofStep, f : Set[Formula] => Set[Formula], fi : Seq[Int] => Seq[Int] = identity, fsub : Seq[Sequent] = Nil) : SCProofStep= pS match
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
            case InstFunSchema(bot, t1, insts)              => InstFunSchema(f(bot.left)|- bot.right, fi(pS.premises).head, insts)
            case InstPredSchema(bot, t1, insts)             => InstPredSchema( f( bot.left )|- bot.right, fi(pS.premises).head, insts)
            case SCSubproof(pp, t, b)                       => {
                SCSubproof(SimpleProofTransformer(pp).transform(fsub.toIndexedSeq ++ t.filter(_ >= 0).map(i => appended_steps(i).bot).toIndexedSeq), fi(t), b)}
    }
}

/**
* If a theory prooves the original theorem, that means we have a proof that proves each imports, we can then cut the premises at the 
* conclusion to get to the original theorem proposition using them to get to the original statement that has been proven.
* The opposite is obviously not the case as we cannot always split the aassumptionns from the conclusion.
**/