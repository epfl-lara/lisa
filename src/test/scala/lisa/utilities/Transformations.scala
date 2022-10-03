package lisa.utilities
import lisa.test.ProofCheckerSuite
import lisa.utils.Printer

import lisa.proven.tactics.Destructors.*
import lisa.proven.tactics.ProofTactics.*

import lisa.kernel.proof.SCProof
import org.scalatest.funsuite.AnyFunSuite
import scala.language.adhocExtensions
import lisa.kernel.fol.*
import scala.collection.immutable.NumericRange
class Transformations extends ProofCheckerSuite {
    import lisa.proven.SetTheoryLibrary.*

    trait Tree {
        val head : Any
        val children : Seq[Tree]
    }

    case class Leaf() extends Tree {
        val children = Seq.empty
        val head = Seq.empty
    }

    case class Node(h : Any, c: Array[Tree]) extends Tree {
        val children = c.toSeq
        val head = h
    }

    implicit def nullToLeaf(x: Seq[_]) : Leaf =Leaf()

    extension (x: Any){
        def -> (y: Array[Tree]): Tree = Node(x, y) 
    }
    val * = Seq.empty
    implicit 
    val test : Tree = * -> Array(*,* -> Array(*,*,*,*))


    def dummyProof(depth : NumericRange[Long], nVars : NumericRange[Long], withImports : Boolean) : SCProof = {
        val rand = new scala.util.Random
        val trueDepth = rand.between(depth.start, depth.end)
        

        def leaf (ind : Seq[Int]) = {
            val le = SchematicNPredicateLabel("phi_" + ind.mkString("_"), 0)()
            Hypothesis(le |- le, le) }

        def parent (children : Seq[SCProofStep]) = {
            val cunjuncts = children.zipWithIndex.filter(_ => rand.nextBoolean())
            val nCunjuncts = children.zipWithIndex.filterNot(_ => rand.nextBoolean())

            if ( rand.nextBoolean()) {
                RightAnd(children.flatMap(_.bot.left) |- (nCunjuncts.map(_._1.bot.right).flatten :+ ConnectorFormula(And, cunjuncts.flatMap(_._1.bot.right))), cunjuncts.map(_._2), cunjuncts.map(_._1.bot.right).flatten)
            } else {
                LeftOr((ConnectorFormula(Or, cunjuncts.flatMap(_._1.bot.left)) +: nCunjuncts.map(_._1.bot.left).flatten) |- (children.flatMap(_.bot.right)), cunjuncts.map(_._2), cunjuncts.map(_._1.bot.left).flatten)
            }
        }
        
        SCProof()
    }
    
    test("Trasnsformation initialises well with empty proof and returns an empty proof") {
        val nullSCProof = SCProof()
        val transf = lisa.utilities.prooftransform.ProofUnconditionalizer(nullSCProof)
        (checkProof(dummyProof((5L to 6L), (1L to 2L), false)))
        assert(transf.transform() == nullSCProof)
        
    }

    /**
     * Any proof where there are no imports shoud not be modified 
     * Dummy proofs of varying size should be tested
     **/
    test("A proof with no imports is not modified") {
        val phi = SchematicNPredicateLabel("phi", 0)

        val intro = Hypothesis((phi()) |- (phi()), phi())
        val outro = Rewrite((phi()) |- (phi()), 0)
        
        val noImpProof = SCProof(IndexedSeq(intro, outro), IndexedSeq.empty)
        val transf = lisa.utilities.prooftransform.ProofUnconditionalizer(noImpProof)
        assert((transf.transform() == noImpProof))
        checkProof(noImpProof)
    }

   test("A proof with an imports is to be modified") {
        val phi = SchematicNPredicateLabel("phi", 0)

        val intro = Rewrite(() |- (phi()), -1)
        val outro = Weakening(phi() |- (phi()), 0)
        
        val noImpProof = SCProof(IndexedSeq(intro, outro), IndexedSeq(intro.bot))
        val transf = lisa.utilities.prooftransform.ProofUnconditionalizer(noImpProof).transform()
        info(Printer.prettySequent(transf.steps.head.bot))
        assert(transf != noImpProof )
        
    }

}
