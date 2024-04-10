package lisa.maths.settheory.types.adt

import lisa.maths.settheory.SetTheory.{*, given}
import ADTDefinitions.*
import Helpers.*

class Induction(adt: SemanticADT) extends lisa.prooflib.ProofTacticLib.ProofTactic {



  private def prove(using proof: lisa.SetTheoryLibrary.Proof)(subproofs: Map[SemanticConstructor, (Seq[Variable], proof.Fact)])(bot: Sequent) =

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

  def apply(using proof: lisa.SetTheoryLibrary.Proof)(cases: ADTSyntax.CaseBuilder[proof.ProofStep] ?=> Unit)(bot: Sequent) = 
    val builder = ADTSyntax.CaseBuilder[proof.ProofStep]
    cases(using builder)
    prove(using proof)(builder.build)(bot)
}

object Induction {
  def apply(adt: ADT) = new Induction(adt.underlying)
}