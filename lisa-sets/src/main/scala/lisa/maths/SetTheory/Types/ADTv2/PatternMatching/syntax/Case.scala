package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.syntax

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.interface.Constructor
import lisa.maths.SetTheory.Types.ADTv2.interface.SpecializedADT
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.PatternValidation
import lisa.maths.SetTheory.Types.ADTv2.PatternMatching.semantics.nested.NestedConstructorPattern
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.appSeq
import lisa.maths.SetTheory.Types.TypingHelpers.::

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
    PatternValidation.validateCase(cons, args, adt).fold(message => throw new IllegalArgumentException(message), identity)
    val typeArgs = adt.typeArgs
    val pattern = NestedConstructorPattern.fromArgs(
      cons.semantic,
      args.map {
        case v: Variable[Ind] => Left(v)
        case term => Right(term)
      },
      ∅,
      cons.semantic.typeVariablesSeq.zip(typeArgs).map((v, typ) => v := typ),
      adt.term
    )
    val vars = pattern.topBinders
    val prop = bot.right.head
    val consTerm = appSeq(cons.semantic.term(typeArgs))(vars)
    val subst = adtVar -> consTerm

    val assumptions = pattern.typingPremises
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
  def apply(body: Expr[Ind])(using builder: CaseAccumulator[Expr[Ind], Unit]): Unit =
    builder += (cons, args, body)
}
