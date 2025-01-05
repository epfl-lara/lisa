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
  * have(forall(x, x :: adt => P(x)) /*or*/ x :: adt |- P(x)) by Induction(x, adt) {
  *   Case(c1, x1, ..., xn) subproof {
  *     // proof of P(xi) /\ ... P(xj) => P(c1(x1, ..., xn))
  *   }
  *   ...
  *   Case(cm, x1, ..., xk) subproof {
  *     // proof of P(xi) /\ ... P(xj) => P(c1(x1, ..., xn'))
  *   }
  * }
  * }}}
  * 
  * x and adt are inferred from the context if not provided by the user.
  * 
  * Supports only 1 formula on the right hand side of the sequent.
  * @param expectedVar the variable on which the induction is performed
  * @param expectedADT the algebraic data type on which the induction is performed
  */
class Induction[M <: Arity](expectedVar: Option[Variable], expectedADT: Option[ADT[M]]) extends lisa.prooflib.ProofTacticLib.ProofTactic {

  /**
    * Given a proof of the claim for each case (possibly using the induction hypothesis), 
    * reassemble them to generate a proof of the claim of the form
    *   `∀x. x :: adt => P(x)`
    *
    * @param proof the proof in which the induction is performed
    * @param cases the proofs of the claim for each case in addition to the variables used by the user
    * @param inductionVariable the variable over which the induction is performed
    * @param adt the algebraic data type to perform induction on
    * @param prop the property to prove //TODO: Change to a lambda expression (Scala 3.4.2)
    */
  private def proveForallPredicate[N <: Arity](using proof: lisa.SetTheoryLibrary.Proof)(cases: Map[Constructor[N], (Seq[Variable], proof.Fact)], inductionVariable: Variable, adt: ADT[N], typeVariablesSubst: Seq[Term], propFun: Term => Formula, context: Set[Formula]): proof.Fact =

    val prop = lambda[Term, Formula](x, propFun(x))
    val typeVariablesSubstPairs = adt.typeVariables.toSeq.zip(typeVariablesSubst).map(SubstPair(_, _))
    val instTerm = adt(typeVariablesSubst*)

    adt.constructors.foldLeft[proof.Fact](adt.induction.of((typeVariablesSubstPairs :+ (P := prop))*)) ( (acc, c) =>
      val inductiveCaseProof = cases(c)._1.zip(c.underlying.underlying.specification.map(_.substitute(typeVariablesSubstPairs*))).foldRight[proof.Fact](cases(c)._2) ( (el, acc2) =>
        val (v, ty) = el
        val accRight: Formula = acc2.statement.right.head
        ty match 
          case Self => 
            have((acc2.statement -<? prop(v)).left |- prop(v) ==> accRight) by Weakening(acc2)
            thenHave((lastStep.statement -<? (v :: instTerm)).left |- v :: instTerm ==> (prop(v) ==> accRight)) by Weakening
            thenHave(lastStep.statement.left |- forall(v, v :: instTerm ==> (prop(v) ==> accRight))) by RightForall
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
    thenHave(context |- forall(inductionVariable, inductionVariable :: instTerm ==> prop(inductionVariable))) by Tautology //Change


  
  /**
    * Infers the variable, the ADT and the arguments of the ADT from a formula of the form `x :: ADT(T1, ..., Tn)`.
    *
    * @param f the formula to infer these elements from
    */
  def inferArguments(f: Formula): Option[(Variable, ADT[?], Seq[Term])] =
    def checkFoundArguments(foundVar: Variable, foundADT: ADT[?], args: Seq[Term]): Option[(Variable, ADT[?], Seq[Term])] = 
      (expectedVar, expectedADT) match 
        case (Some(v), _) if v != foundVar => None
        case (_, Some(a)) if a != foundADT => None
        case _ => Some((foundVar, foundADT, args))
    
    f match
      case TypeAssignment(Variable(id), ADT(foundADT, args)) => 
        checkFoundArguments(Variable(id), foundADT, args)
      case AppliedPredicate(in, Seq[Term](Variable(id), ADT(foundADT, args))) =>
        checkFoundArguments(Variable(id), foundADT, args)
      case _ => 
        None

  /**
    * Infers the variable, the ADT and the arguments of the ADT from a set of formula 
    * containing one is of the form `x :: ADT(T1, ..., Tn)`.
    *
    * @param s the set of formula to infer these elements from
    */
  def inferArguments(s: Set[Formula]): Option[(Variable, ADT[?], Seq[Term])] =
    s.foldLeft[Option[(Variable, ADT[?], Seq[Term])]](None)((acc, prem) => 
      acc.orElse(inferArguments(prem))
  )

  /**
    * Infers the variable, the ADT and the arguments of the ADT from a sequent whose one of the premises
    * is of the form `x :: ADT(T1, ..., Tn)`.
    *
    * @param seq the sequent to infer these elements from
    */
  def inferArguments(seq: Sequent): Option[(Variable, ADT[?], Seq[Term], Option[Formula])] =
     inferArguments(seq.left).map(p => (p._1, p._2, p._3, None))
    .orElse(
      seq.right.head match
        case Forall(x, Implies(assignment, prop)) =>
          inferArguments(assignment).filter(p => p._1 == x).map(p => (p._1, p._2, p._3, Some(prop)))
        case _ => None
    )
  
  /**
    * Given a proof of the claim for each case (possibly using the induction hypothesis), 
    * reassemble the subproofs to generate a proof of the claim for every element of the ADT.
    * 
    * @tparam N the arity of the ADT
    * @param proof the scope in which the induction is performed
    * @param cases the cases to prove. A [[CaseBuilder]] is a mutable data structure that register every case that
    * has been added to the tactic.
    * @param bot the claim
    */
  def apply[N <: Arity](using proof: lisa.SetTheoryLibrary.Proof)(cases: ADTSyntax.CaseBuilder[N, proof.ProofStep, (Sequent, Seq[Term], Variable)] ?=> Unit)(bot: Sequent): proof.ProofTacticJudgement = 
    inferArguments(bot) match 
      case Some((inferedVar, inferedADT, inferedArgs, inferedProp)) => 

        val prop = inferedProp.getOrElse(bot.right.head)
        val propFunction = (t: Term) => inferedProp.getOrElse(bot.right.head).substitute(inferedVar -> t)
        val assignment = inferedVar :: inferedADT(inferedArgs*)
        val context = (if inferedProp.isDefined then bot else bot -<< assignment).left
        val builder = ADTSyntax.CaseBuilder[N, proof.ProofStep, (Sequent, Seq[Term], Variable)]((context |- prop, inferedArgs, inferedVar))
        cases(using builder)
        
        builder.isValid(inferedADT.asInstanceOf[ADT[N]]) match
          case None => 
            TacticSubproof { sp ?=> 
              proveForallPredicate(using sp)(builder.build, inferedVar, inferedADT.asInstanceOf[ADT[N]], inferedArgs, propFunction, context)
              if !inferedProp.isDefined then
                lastStep.statement.right.head match
                  case Forall(_, phi) =>
                    thenHave(context |- phi) by InstantiateForall(inferedVar)
                  case _ => throw UnreachableException

              thenHave(bot) by Tautology
            } 
          case Some(msg) => proof.InvalidProofTactic(msg)

      case None => proof.InvalidProofTactic("No variable typed with the ADT found in the context.")
    
}

/**
  * Companion object for the [[Induction]] tactic class.
  */
object Induction {
  def apply()(using proof: lisa.SetTheoryLibrary.Proof) = new Induction(None, None)
  def apply[N <: Arity](adt: ADT[N])(using proof: lisa.SetTheoryLibrary.Proof) = new Induction(None, Some(adt))
  def apply(v: Variable)(using proof: lisa.SetTheoryLibrary.Proof) = new Induction(Some(v), None)
  def apply[N <: Arity](v: Variable, adt: ADT[N])(using proof: lisa.SetTheoryLibrary.Proof) = new Induction(Some(v), Some(adt))
}