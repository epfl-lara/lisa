package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.syntax

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.PatternValidation
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.Pattern
import lisa.maths.SetTheory.Types.ADTv2.interface.Constructor
import lisa.maths.SetTheory.Types.ADTv2.interface.SpecializedADT

case class Case(cons: Constructor[?], args: Expr[Ind]*) {

  /**
   *  Used in the context of an induction proof. Adds the subproof corresponding to this
   *  case into a builder.
   *
   *  Concrete terms are compiled to fresh binders plus equality assumptions, so nested
   *  constructor-headed patterns such as `cons(tru, tl)` are accepted here as well.
   *
   *  @see [[lisa.maths.SetTheory.Types.ADTv2.tactics.Induction]]
   */
  def subproof(using
      proof: Proof,
      line: sourcecode.Line,
      file: sourcecode.File,
      builder: CaseAccumulator[proof.ProofStep, (Sequent, SpecializedADT[?], Variable[Ind])]
  )(subproof: proof.InnerProof ?=> Unit): Unit =
    val (bot, adt, adtVar) = builder.comp
    val resolved = PatternValidation.resolveCase(cons, args, adt).fold(message => throw new IllegalArgumentException(message), identity)
    val pattern = Pattern.fromResolved(
      resolved,
      bot.left.toSeq ++ bot.right.toSeq :+ adtVar
    )
    val vars = pattern.topBinders
    val prop = bot.right.head
    val consTerm = pattern.inputTerm
    val subst = adtVar -> consTerm

    val assumptions = pattern.typingPremises
      ++ cons.semantic
        .recursiveBinders(vars)
        .map(v => prop.substitute(adtVar -> v))
      ++ pattern.guards.map(guard => guard.binder === guard.guardTerm)

    val botWithAssumptions = bot.substitute(subst) ++ (assumptions |- ())

    val iProof: proof.InnerProof = new proof.InnerProof(Some(botWithAssumptions))
    subproof(using iProof)
    val proofStep = (new SUBPROOF(using proof)(None)(iProof)).judgement
      .validate(line, file)
      .asInstanceOf[proof.ProofStep]

    def subproofWithExtraStep: proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      val fullSeq =
        Tautology(using lisa.SetTheoryLibrary, ip)(proofStep)(botWithAssumptions)
      if fullSeq.isValid then fullSeq.validate(line, file)
      else return proof.InvalidProofTactic(s"Proof of case ${cons.name} is invalid.\nExpected: ${botWithAssumptions}.")
    }

    builder.addResolved(pattern, subproofWithExtraStep.validate(line, file))

  /**
   *  Used in the context of a function definition. Adds the body of the case to a
   *  builder.
   *
   *  Arguments may be binder variables or concrete terms (nested patterns).
   *
   *  @param body the body of this case
   *  @param builder the builder for the function definition
   */
  def apply(body: Expr[Ind])(using builder: CaseAccumulator[Expr[Ind], Unit]): Unit =
    builder += (cons, args, body)
}
