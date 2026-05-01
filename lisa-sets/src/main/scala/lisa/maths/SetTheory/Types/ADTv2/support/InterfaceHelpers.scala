package lisa.maths.SetTheory.Types.ADTv2.support

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Functions.Function.app
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.{forallSeq, UnreachableException, f, a, b, x}
import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.funEqDef
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
      else
        grouped.update(variable, variable := value)
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
    substitutions.map(substitution =>
      substitution._1.asInstanceOf[Variable[Ind]] -> substitution._2.asInstanceOf[Expr[Ind]]
    ).toMap

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

  def instantiatedSemanticSignature(
      signature: Seq[(Variable[Ind], Expr[Ind])],
      substitutions: Seq[TypeSubstitution]
  ): Seq[(Variable[Ind], Expr[Ind])] =
    signature.map((variable, typ) => variable -> specializeTerm(typ, substitutions))

  def proveAppliedTyping(using proof: lisa.SetTheoryLibrary.Proof)(
      headTyping: proof.Fact,
      headTerm: Expr[Ind],
      headType: Expr[Ind],
      args: Seq[(Variable[Ind], Expr[Ind])]
  ): proof.Fact =
    args.foldLeft[(proof.Fact, Expr[Ind], Expr[Ind])]((headTyping, headTerm, headType)) {
      case ((accFact, accTerm, accType), (argument, argumentType)) =>
        accType match
          case domainType ->: codomainType =>
            val argumentTyping = assume(argument :: domainType)
            val nextFact = have(app(accTerm)(argument) :: codomainType) by Tautology.from(
              accFact,
              funEqDef of (
                f := accTerm,
                a := domainType,
                b := codomainType,
                x := argument
              ),
              argumentTyping
            )
            (nextFact, app(accTerm)(argument), codomainType)
          case _ => throw UnreachableException
    }._1
}
