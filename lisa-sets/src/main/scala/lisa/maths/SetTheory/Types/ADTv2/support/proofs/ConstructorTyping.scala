package lisa.maths.SetTheory.Types.ADTv2.support.proofs

import lisa.maths.SetTheory.Functions.Pi.->:
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticConstructor
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils._
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.funEqDef
import lisa.maths.SetTheory.Types.TypingHelpers._
import lisa.utils.prooflib.BasicStepTactic.Restate
import lisa.utils.prooflib.ProofTacticLib.Arity

object ConstructorTyping {

  def constructorApplicationTyping[N <: Arity](
      c: SemanticConstructor[N],
      args: Seq[Variable[Ind]]
  ): THM = Lemma(
    wellTypedFormula(c.semanticSignature(args)) |- (c.appliedTerm(args) :: c.adt.term)
  ) {
    have(c.term(c.typeVariablesSeq) :: c.typ) by Restate.from(c.intro)
    val introTyping = lastStep
    val argsWellTyped = assume(wellTypedFormula(c.semanticSignature(args)))

    val finalTyping = args.foldLeft(
      (introTyping, c.term(c.typeVariablesSeq): Expr[Ind], c.typ: Expr[Ind])
    ) { case ((accFact, accTerm, accType), argument) =>
      accType match
        case domainTy ->: codomainTy =>
          val argumentTyping = have(
            wellTypedFormula(c.semanticSignature(args)) |- argument :: domainTy
          ) by Tautology.from(argsWellTyped)
          val nextTyping = have(
            wellTypedFormula(c.semanticSignature(args)) |- (accTerm * argument) :: codomainTy
          ) by Tautology.from(
            accFact,
            funEqDef of (f := accTerm, a := domainTy, b := codomainTy, x := argument),
            argumentTyping
          )
          (nextTyping, accTerm * argument, codomainTy)
        case _ => throw UnreachableException
    }._1

    have(thesis) by Restate.from(finalTyping)
  }
}
