package lisa.maths.SetTheory.Types.ADTv2.support

import lisa.maths.SetTheory.Functions.Function.app
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.utils.prooflib.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.UnreachableException
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.a
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.b
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.f
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.forallSeq
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.x
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Types.TypingTheorems.arrowElim
import lisa.utils.fol.FOL.SubstPair

object InterfaceHelpers {

  type TypeSubstitution = SubstPair { type S = Ind }

  def normalizeTypeSubstitutions(
      ownerKind: String,
      ownerName: String,
      typeVariables: Seq[Variable[Ind]],
      substitutions: Seq[TypeSubstitution]
  ): Seq[TypeSubstitution] = {
    val allowed = typeVariables.toSet
    val grouped = scala.collection.mutable.LinkedHashMap.empty[Variable[Ind], TypeSubstitution]

    substitutions.foreach { substitution =>
      val variable = substitution._1.asInstanceOf[Variable[Ind]]
      val value = substitution._2.asInstanceOf[Expr[Ind]]
      require(
        allowed.contains(variable),
        s"$ownerKind $ownerName cannot substitute non-type variable $variable."
      )
      if grouped.contains(variable) then
        val previous = grouped(variable)
        require(
          previous._2.asInstanceOf[Expr[Ind]] == value,
          s"$ownerKind $ownerName received incompatible substitutions for $variable."
        )
      else grouped.update(variable, variable := value)
    }

    typeVariables.flatMap(grouped.get)
  }

  def getRemainingTypeVariables(
      typeVariables: Seq[Variable[Ind]],
      substitutions: Seq[TypeSubstitution]
  ): Seq[Variable[Ind]] = {
    val substituted = substitutions.map(_._1.asInstanceOf[Variable[Ind]]).toSet
    typeVariables.filterNot(substituted.contains)
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

  def substitutionMap(
      substitutions: Seq[TypeSubstitution]
  ): Map[Variable[Ind], Expr[Ind]] =
    substitutions.map(substitution => substitution._1.asInstanceOf[Variable[Ind]] -> substitution._2.asInstanceOf[Expr[Ind]]).toMap

  def resolvedTypeArguments(
      typeVariables: Seq[Variable[Ind]],
      substitutions: Seq[TypeSubstitution]
  ): Seq[Expr[Ind]] = {
    val mapping = substitutionMap(substitutions)
    typeVariables.map(variable => mapping.getOrElse(variable, variable))
  }

  def specializeTerm(term: Expr[Ind], substitutions: Seq[TypeSubstitution]): Expr[Ind] =
    term.substitute(substitutions*)

  def specializeFormula(
      formula: Expr[Prop],
      substitutions: Seq[TypeSubstitution]
  ): Expr[Prop] =
    formula.substitute(substitutions*)

  def quantifiedTypeFormula(
      formula: Expr[Prop],
      typeVariables: Seq[Variable[Ind]],
      substitutions: Seq[TypeSubstitution]
  ): Expr[Prop] =
    forallSeq(
      getRemainingTypeVariables(typeVariables, substitutions),
      specializeFormula(formula, substitutions)
    )

  def formulaOf(statement: Sequent, owner: String): Expr[Prop] = {
    require(
      statement.left.isEmpty && statement.right.size == 1,
      s"$owner expects a single-formula theorem statement, got $statement."
    )
    statement.right.head
  }

  def quantifiedTypeStatement(
      statement: Sequent,
      typeVariables: Seq[Variable[Ind]],
      substitutions: Seq[TypeSubstitution],
      owner: String
  ): Expr[Prop] =
    quantifiedTypeFormula(formulaOf(statement, owner), typeVariables, substitutions)

  def requireMonomorphicAccess(ownerKind: String, ownerName: String, typeVariables: Seq[Variable[Ind]]): Unit =
    require(
      typeVariables.isEmpty,
      s"$ownerKind $ownerName expects ${typeVariables.size} type argument(s)."
    )

  def instantiatedSemanticSignature(
      signature: Seq[(Variable[Ind], Expr[Ind])],
      substitutions: Seq[TypeSubstitution]
  ): Seq[(Variable[Ind], Expr[Ind])] =
    signature.map((variable, typ) => variable -> specializeTerm(typ, substitutions))

  def proveAppliedTyping(using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      headTyping: proof.Fact,
      headTerm: Expr[Ind],
      headType: Expr[Ind],
      args: Seq[(Variable[Ind], Expr[Ind])]
  ): proof.Fact =
    args
      .foldLeft[(proof.Fact, Expr[Ind], Expr[Ind])]((headTyping, headTerm, headType)) { case ((accFact, accTerm, accType), (argument, _)) =>
        accType match
          case domainType ->: codomainType =>
            val argumentTyping = assume(argument :: domainType)
            val nextFact = have(app(accTerm)(argument) :: codomainType) by Tautology.from(
              accFact,
              arrowElim of (
                f := accTerm,
                a := domainType,
                b := codomainType,
                x := argument
              ),
              argumentTyping
            )
            (nextFact, app(accTerm)(argument), codomainType)
          case _ => throw UnreachableException
      }
      ._1

  /**
   * The general form of `baseTheorem`, universally closed over the owner's type
   * variables. A caller wanting it at specific type arguments instantiates this with
   * `of` rather than asking for a separately proved copy.
   *
   * A monomorphic owner has nothing to close over, so the base theorem is returned
   * unchanged and no derived theorem is created at all.
   */
  def generalTheorem(using
      line: sourcecode.Line,
      file: sourcecode.File
  )(
      displayName: String,
      typeVariables: Seq[Variable[Ind]],
      suffix: String,
      baseTheorem: THM
  ): THM =
    if typeVariables.isEmpty then baseTheorem
    else
      val theoremName = s"$displayName/$suffix"
      THM(
        forallSeq(typeVariables, formulaOf(baseTheorem.statement, theoremName)),
        theoremName,
        line.value,
        file.value,
        Theorem
      ) {
        have(baseTheorem.statement) by Restate.from(baseTheorem)
        thenHave(thesis) by QuantifiersIntro(typeVariables)
      }

  /**
   * A copy of `baseTheorem` with type variables substituted away.
   *
   * Unlike the user-facing accessors, which expose one general theorem and let callers
   * instantiate it with `of`, the internal height machinery needs a standalone theorem
   * outside any proof, so it still pays for a derived copy per instantiation.
   */
  def instantiatedTheorem(using
      line: sourcecode.Line,
      file: sourcecode.File
  )(
      theoremOwner: String,
      suffix: String,
      substitutions: Seq[TypeSubstitution],
      baseTheorem: THM
  ): THM = {
    val theoremName = s"$theoremOwner/$suffix"
    THM(
      baseTheorem.statement.substitute(substitutions*),
      theoremName,
      line.value,
      file.value,
      Theorem
    ) {
      have(thesis) by Restate.from(baseTheorem.of(substitutions*))
    }
  }

  /**
   * The applied ("curried") form of a typing introduction rule. Unlike
   * [[generalTheorem]] this is a genuinely derived statement rather than an instance of
   * the base one, so it is proved once, in general form, over the owner's type
   * variables; callers instantiate it with `of`.
   */
  def introAppTheorem(using
      line: sourcecode.Line,
      file: sourcecode.File
  )(
      displayName: String,
      baseTheorem: THM,
      headTerm: Expr[Ind],
      headType: Expr[Ind],
      assumptions: Set[Expr[Prop]],
      typingArgs: Seq[(Variable[Ind], Expr[Ind])],
      conclusion: Expr[Prop]
  ): THM =
    THM(
      assumptions |- conclusion,
      s"$displayName/introApp",
      line.value,
      file.value,
      Theorem
    ) {
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
