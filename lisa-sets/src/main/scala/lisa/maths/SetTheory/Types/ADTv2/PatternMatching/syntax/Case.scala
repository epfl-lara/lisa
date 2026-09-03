package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.syntax

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.interface.Constructor
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.appSeq
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.wellTypedSet
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.prooflib.ProofTacticLib.Arity

case class Case[N <: Arity](cons: Constructor[N], args: Expr[Ind]*) {

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
      builder: CaseAccumulator[N, proof.ProofStep, (Sequent, Seq[Expr[Ind]], Variable[Ind])]
  )(subproof: proof.InnerProof ?=> Unit): Unit =
    val vars: Seq[Variable[Ind]] = args.zipWithIndex.map {
      case (v: Variable[Ind], _) => v
      case (_, i) => variable[Ind](s"${cons.semantic.name}/arg$i")
    }

    val (bot, typeArgs, adtVar) = builder.comp
    val prop = bot.right.head
    val consTerm = appSeq(cons.semantic.term(typeArgs))(vars)
    val subst = adtVar -> consTerm

    val assumptions = wellTypedSet(
      cons.semantic
        .semanticSignature(vars)
        .map(p =>
          (
            p._1,
            p._2.substitute(cons.semantic.typeVariablesSeq.zip(typeArgs).map(SubstPair(_, _))*)
          )
        )
    ) ++ cons.semantic
      .recursiveBinders(vars)
      .map(v => v :: cons.adt.termAt(typeArgs))
      ++ cons.semantic
        .recursiveBinders(vars)
        .map(v => prop.substitute(adtVar -> v))
      ++ args.zip(vars).collect {
        case (t, v) if !t.isInstanceOf[Variable[Ind]] => v === t
      }

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

    builder += (cons, args, subproofWithExtraStep.validate(line, file))

  /**
   *  Used in the context of a function definition. Adds the body of the case to a
   *  builder.
   *
   *  Arguments may be binder variables or concrete terms (nested patterns).
   *
   *  @param body the body of this case
   *  @param builder the builder for the function definition
   */
  def apply(body: Expr[Ind])(using builder: CaseAccumulator[N, Expr[Ind], Unit]): Unit =
    builder += (cons, args, body)
}
