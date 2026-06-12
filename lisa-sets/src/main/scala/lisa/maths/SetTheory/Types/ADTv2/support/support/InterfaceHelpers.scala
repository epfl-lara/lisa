package lisa.maths.SetTheory.Types.ADTv2.support

import lisa.maths.SetTheory.Functions.Function.app
import lisa.maths.SetTheory.Functions.Predef._
import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.support.core.QuantifiersIntro
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.UnreachableException
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.a
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.b
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.f
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.forallSeq
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.x
import lisa.maths.SetTheory.Types.ADTv2.support.proofs.UsefulTheorems.funEqDef
import lisa.maths.SetTheory.Types.TypingHelpers.::
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

  def proveAppliedTyping(using proof: lisa.SetTheoryLibrary.Proof)(
      headTyping: proof.Fact,
      headTerm: Expr[Ind],
      headType: Expr[Ind],
      args: Seq[(Variable[Ind], Expr[Ind])]
  ): proof.Fact =
    args.foldLeft[(proof.Fact, Expr[Ind], Expr[Ind])]((headTyping, headTerm, headType)) {
      case ((accFact, accTerm, accType), (argument, _)) =>
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

  def theoremAt(using
      line: sourcecode.Line,
      file: sourcecode.File
  )(
      displayName: String,
      typeVariables: Seq[Variable[Ind]],
      typeArgs: Seq[Expr[Ind]],
      suffix: String,
      baseTheorem: THM
  ): THM = {
    require(
      typeArgs.isEmpty || typeArgs.size == typeVariables.size,
      s"$displayName expects ${typeVariables.size} type argument(s), got ${typeArgs.size}."
    )
    val substitutions =
      if typeArgs.isEmpty then Seq.empty
      else typeVariables.zip(typeArgs).map((variable, arg) => variable := arg)
    val theoremOwner =
      if typeArgs.isEmpty then displayName
      else Utils.renderAppliedSymbol(displayName, typeVariables.size, typeArgs)
    val theoremName = s"$theoremOwner/$suffix"

    THM(
      quantifiedTypeStatement(
        baseTheorem.statement,
        typeVariables,
        substitutions,
        theoremName
      ),
      theoremName,
      line.value,
      file.value,
      Theorem
    ) {
      have(baseTheorem.statement.substitute(substitutions*)) by
        Restate.from(baseTheorem.of(substitutions*))
      thenHave(thesis) by QuantifiersIntro(getRemainingTypeVariables(typeVariables, substitutions))
    }
  }

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

  def introAppAt(using
      line: sourcecode.Line,
      file: sourcecode.File
  )(
      displayName: String,
      typeVariables: Seq[Variable[Ind]],
      typeArgs: Seq[Expr[Ind]],
      baseTheorem: THM,
      headTermAt: Seq[Expr[Ind]] => Expr[Ind],
      headTypeAt: Seq[TypeSubstitution] => Expr[Ind],
      assumptionsAt: Seq[TypeSubstitution] => Set[Expr[Prop]],
      typingArgsAt: Seq[TypeSubstitution] => Seq[(Variable[Ind], Expr[Ind])],
      conclusionAt: Seq[TypeSubstitution] => Expr[Prop]
  ): THM = {
    require(
      typeArgs.isEmpty || typeArgs.size == typeVariables.size,
      s"$displayName expects ${typeVariables.size} type argument(s), got ${typeArgs.size}."
    )
    val substitutions =
      if typeArgs.isEmpty then Seq.empty
      else typeVariables.zip(typeArgs).map((variable, arg) => variable := arg)
    val theoremOwner =
      if typeArgs.isEmpty then displayName
      else Utils.renderAppliedSymbol(displayName, typeVariables.size, typeArgs)
    val theoremName = s"$theoremOwner/introApp"
    val headTerm = headTermAt(typeArgs)
    val headType = headTypeAt(substitutions)
    val typingArgs = typingArgsAt(substitutions)

    THM(
      assumptionsAt(substitutions) |- conclusionAt(substitutions),
      theoremName,
      line.value,
      file.value,
      Theorem
    ) {
      have(baseTheorem.statement.substitute(substitutions*)) by
        Restate.from(baseTheorem.of(substitutions*))

      val appliedTyping = proveAppliedTyping(
        headTyping = lastStep,
        headTerm = headTerm,
        headType = headType,
        args = typingArgs
      )

      have(thesis) by Tautology.from(appliedTyping)
    }
  }
}
