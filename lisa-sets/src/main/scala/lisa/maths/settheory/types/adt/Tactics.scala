/**
  * Defines a set of tactics to reason on Algebraic Data Types
  */

package lisa.maths.settheory.types.adt

import lisa.maths.settheory.SetTheory.{*, given}
import ADTDefinitions.*
import Helpers.*

/**
  * Tactic performing a structural induction proof over an algebraic data type.
  * 
  * ===Usage===
  * {{{
  * have(forall(x, x :: adt => P(x))) by Induction(adt) {
  *   Case(c1, x1, ..., xn) subproof {
  *     // proof of P(xi) /\ ... P(xj) => P(c1(x1, ..., xn))
  *   }
  *   ...
  *   Case(cm, x1, ..., xk) subproof {
  *     // proof of P(xi) /\ ... P(xj) => P(c1(x1, ..., xn'))
  *   }
  * }
  * }}}
  * @param adt the algebraic data type to perform induction on
  */
class Induction[N <: Arity](adt: SemanticADT[N]) extends lisa.prooflib.ProofTacticLib.ProofTactic {

  /**
    * Given a proof of the claim for each case (possibly using the induction hypothesis), reassemble the subproofs to generate
    * a proof of the claim for every element of the ADT.
    *
    * @param proof the scope in which the induction is performed
    * @param subproofs the proofs of the claim for each case in addition to the variables used by the user
    * @param bot the claim
    */
  private def prove(using proof: lisa.SetTheoryLibrary.Proof)(subproofs: Map[SemanticConstructor[N], (Seq[Variable], proof.Fact)])(bot: Sequent) =

    val P = predicate[1]

    TacticSubproof {
      sp ?=>

        bot.right.head match 
          case Forall(x, Implies(in(y, t), prop)) if y == x => 

            val ccl = (v: Term) => prop.substitute(x -> v)


            adt.constructors.foldLeft[sp.Fact](adt.induction of (P := lambda(x, ccl(x)))) ( (acc, c) =>
              val inductiveCaseProof = subproofs(c)._1.zip(c.underlying.specification).foldRight[sp.Fact](subproofs(c)._2) ( (el, acc2) =>
                val (v, ty) = el
                val accRight: Formula = acc2.statement.right.head
                ty match 
                  case Self => 
                    have((acc2.statement -<? ccl(v)).left |- ccl(v) ==> accRight) by Weakening(acc2)
                    thenHave((lastStep.statement -<? (v :: adt.term)).left |- v :: adt.term ==> (ccl(v) ==> accRight)) by Weakening
                    thenHave(lastStep.statement.left |- forall(v, v :: adt.term ==> (ccl(v) ==> accRight))) by RightForall
                  case GroundType(t)=> 
                    thenHave((acc2.statement -<? (v :: t)).left |- v :: t ==> accRight) by Weakening
                    thenHave(lastStep.statement.left |- forall(v, v :: t ==> accRight)) by RightForall
              )
              acc.statement.right.head match 
                case Implies(trueInd, rest) => 
                  // println(s"Case: ${c.fullName}")
                  // println(isSame(trueInd, inductiveCaseProof.statement.right.head))
                  // println(inductiveCaseProof.statement)
                  // println("         +          ")
                  // println(acc.statement)
                  // println("         =          ")
                  // println((acc.statement.left ++ inductiveCaseProof.statement.left) |- rest)
                  have((acc.statement.left ++ inductiveCaseProof.statement.left) |- rest) by Sorry//Cut(inductiveCaseProof, acc)
                case _ => throw UnreachableException
            )
            thenHave(bot) by Tautology //Change
          case _ => UnreachableException
    }

  /**
    * Executes the tactic with a more user-friendly syntax.
    *
    * @param proof the scope in which the induction is performed
    * @param cases the cases to prove. A [[CaseBuilder]] is a mutable data structure that register every case that
    * has been added to the tactic.
    * @param bot the claim
    */
  def apply(using proof: lisa.SetTheoryLibrary.Proof)(cases: ADTSyntax.CaseBuilder[N, proof.ProofStep] ?=> Unit)(bot: Sequent) = 
    val builder = ADTSyntax.CaseBuilder[N, proof.ProofStep]
    cases(using builder)
    prove(using proof)(builder.build)(bot)
}

/**
  * Companion object for the [[Induction]] tactic class.
  */
object Induction {
  def apply[N <: Arity](adt: ADT[N]) = new Induction(adt.underlying)
}