package lisa.maths.SetTheory.Types.ADT.support

import lisa.maths.SetTheory.Functions.Function.app
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADT.support.core.Utils.UnreachableException
import lisa.maths.SetTheory.Types.ADT.support.core.Utils.a
import lisa.maths.SetTheory.Types.ADT.support.core.Utils.b
import lisa.maths.SetTheory.Types.ADT.support.core.Utils.f
import lisa.maths.SetTheory.Types.ADT.support.core.Utils.forallSeq
import lisa.maths.SetTheory.Types.ADT.support.core.Utils.x
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Types.TypingTheorems.arrowElim
import lisa.utils.fol.FOL.SubstPair
import lisa.utils.prooflib.QuantifiersIntro
import lisa.utils.prooflib.Thm

object InterfaceHelpers {

  type TypeSubstitution = SubstPair { type S = Ind }

  /**
   * Validates type substitutions and orders them by the owner's declared parameters.
   */
  def normalizeTypeSubstitutions(
      ownerKind: String,
      ownerName: String,
      typeVariables: Seq[Variable[Ind]],
      substitutions: Seq[TypeSubstitution]
  ): Seq[TypeSubstitution] = {
    val allowed = typeVariables.toSet
    val byVariable = scala.collection.mutable.Map.empty[Variable[Ind], Expr[Ind]]

    substitutions.foreach { substitution =>
      val variable = substitution._1
      val value = substitution._2
      require(
        allowed.contains(variable),
        s"$ownerKind $ownerName cannot substitute non-type variable $variable."
      )
      byVariable.get(variable) match
        case Some(previous) =>
          require(
            previous == value,
            s"$ownerKind $ownerName received incompatible substitutions for $variable."
          )
        case None => byVariable.update(variable, value)
    }

    typeVariables.flatMap(variable => byVariable.get(variable).map(value => variable := value))
  }

  def substitutionsFromArgs(
      ownerKind: String,
      ownerName: String,
      typeVariables: Seq[Variable[Ind]],
      args: Seq[Expr[Ind]]
  ): Seq[TypeSubstitution] = {
    require(
      args.size == typeVariables.size,
      s"$ownerKind $ownerName expects ${typeVariables.size} type argument(s), got ${args.size}."
    )
    typeVariables.zip(args).map((variable, arg) => variable := arg)
  }

  def specializeTerm(term: Expr[Ind], substitutions: Seq[TypeSubstitution]): Expr[Ind] =
    term.substitute(substitutions*)

  def formulaOf(statement: Sequent, owner: String): Expr[Prop] = {
    require(
      statement.left.isEmpty && statement.right.size == 1,
      s"$owner expects a single-formula theorem statement, got $statement."
    )
    statement.right.head
  }

  def instantiatedSemanticSignature(
      signature: Seq[(Variable[Ind], Expr[Ind])],
      substitutions: Seq[TypeSubstitution]
  ): Seq[(Variable[Ind], Expr[Ind])] =
    signature.map((variable, typ) => variable -> specializeTerm(typ, substitutions))

  def proveAppliedTyping(using
      proof: lisa.SetTheoryLibrary.ProofBuilder
  )(
      headTyping: Thm,
      headTerm: Expr[Ind],
      headType: Expr[Ind],
      args: Seq[(Variable[Ind], Expr[Ind])]
  ): Thm =
    args
      .foldLeft[(Thm, Expr[Ind], Expr[Ind])]((headTyping, headTerm, headType)) { case ((accFact, accTerm, accType), (argument, _)) =>
        accType match
          case domainType ->: codomainType =>
            val argumentTyping = assume(argument :: domainType)
            val appliedTerm = app(accTerm)(argument)
            val nextFact = have(appliedTerm :: codomainType) by Tautology.from(
              accFact,
              arrowElim of (
                f := accTerm,
                a := domainType,
                b := codomainType,
                x := argument
              ),
              argumentTyping
            )
            (nextFact, appliedTerm, codomainType)
          case _ => throw UnreachableException
      }
      ._1

  /**
   * Closes a theorem over the type parameters, returning the original when there are none.
   */
  def generalTheorem(using
      line: sourcecode.Line,
      file: sourcecode.File
  )(
      displayName: String,
      typeVariables: Seq[Variable[Ind]],
      suffix: String,
      baseTheorem: Theorem
  ): Theorem =
    if typeVariables.isEmpty then baseTheorem
    else
      val theoremName = s"$displayName/$suffix"
      Theorem.named(theoremName)(forallSeq(typeVariables, formulaOf(baseTheorem.statement, theoremName))) {
        have(baseTheorem.statement) by Restate.from(baseTheorem)
        thenHave(thesis) by QuantifiersIntro(typeVariables)
      }

  /**
   * Instantiates a theorem in the current proof, preserving the original for identity substitutions.
   */
  def instantiate(using
      proof: lisa.SetTheoryLibrary.ProofBuilder
  )(
      baseTheorem: Theorem,
      substitutions: Seq[SubstPair]
  ): Thm = {
    if substitutions.forall(substitution => substitution._1 == substitution._2) then baseTheorem
    else baseTheorem.of(substitutions*)
  }

  /**
   * Derives typing for the symbol applied to its arguments, under their typing assumptions.
   */
  def introAppTheorem(using
      line: sourcecode.Line,
      file: sourcecode.File
  )(
      displayName: String,
      baseTheorem: Theorem,
      headTerm: Expr[Ind],
      headType: Expr[Ind],
      assumptions: Set[Expr[Prop]],
      typingArgs: Seq[(Variable[Ind], Expr[Ind])],
      conclusion: Expr[Prop]
  ): Theorem =
    Theorem.named(s"$displayName/introApp")(assumptions |- conclusion) {
      have(baseTheorem.statement) by Restate.from(baseTheorem)
      val appliedTyping = proveAppliedTyping(
        headTyping = lastStep,
        headTerm = headTerm,
        headType = headType,
        args = typingArgs
      )
      have(thesis) by Tautology.from(appliedTyping)
    }
}
