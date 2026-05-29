package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.syntax

import lisa.maths.SetTheory.Types.ADTv2.interface.Constructor
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.{appSeq, wellTypedSet}

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity

case class Case[N <: Arity](cons: Constructor[N], vars: Variable[Ind]*) {

  /**
   *  Used in the context of an induction proof. Adds the subproof corresponding to this
   *  case into a builder.
   *
   *  @see [[lisa.maths.SetTheory.Types.ADTv2.tactics.Induction]]
   *
   *  @param proof the outer scope of the induction proof
   *  @param line the line at which this case is defined. Usually fetched automatically by
   *    the compiler. Used for error reporting
   *  @param file the file in which this case is defined. Usually fetched automatically by
   *    the compiler. Used for error reporting
   *  @param builder the builder of the induction proof
   *  @param subproof the proof of the case (possibly using the induction hypothesis)
   */
  def subproof(using
      proof: Proof,
      line: sourcecode.Line,
      file: sourcecode.File,
      builder: CaseAccumulator[N, proof.ProofStep, (Sequent, Seq[Expr[Ind]], Variable[Ind])]
  )(subproof: proof.InnerProof ?=> Unit): Unit =
    val (bot, args, adtVar) = builder.comp
    val prop = bot.right.head
    val consTerm = appSeq(cons.semantic.term(args))(vars)
    val subst = adtVar -> consTerm

    val assumptions = wellTypedSet(cons.semantic.semanticSignature(vars).map(p =>
      (
        p._1,
        p._2.substitute(cons.semantic.typeVariablesSeq.zip(args).map(SubstPair(_, _))*)
      )
    )) ++ cons.semantic.syntacticSignature(vars).filter(_._2 == SelfRef)
      .map((v, _) => prop.substitute(adtVar -> v))

    val botWithAssumptions = bot.substitute(subst) ++ (assumptions |- ())

    val iProof: proof.InnerProof = new proof.InnerProof(Some(botWithAssumptions))
    subproof(using iProof)
    val proofStep = (new SUBPROOF(using proof)(None)(iProof)).judgement
      .validate(line, file).asInstanceOf[proof.ProofStep]

    def subproofWithExtraStep: proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      val fullSeq =
        Tautology(using lisa.SetTheoryLibrary, ip)(proofStep)(botWithAssumptions)
      if fullSeq.isValid then fullSeq.validate(line, file)
      else
        return proof.InvalidProofTactic(s"Proof of case ${cons
            .name} is invalid.\nExpected: ${botWithAssumptions}.")
    }

    builder += (cons, (vars, subproofWithExtraStep.validate(line, file)))

  /**
   *  Used in the context of a function definition. Adds the body of the case to a
   *  builder.
   *
   *  @param body the body of this case
   *  @param builder the builder for the function definition
   */
  def apply(body: Expr[Ind])(using builder: CaseAccumulator[N, Expr[Ind], Unit]) = builder +=
    (cons, (vars, body))
}
