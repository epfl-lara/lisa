package lisa.maths.SetTheory.Types.ADTv2.PatternMatching.syntax

import lisa.maths.SetTheory.Types.ADTv2.interface.{ADT, Constructor}
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 * Mutable accumulator collecting constructor cases and validating pattern-matching coverage.
 */
class CaseAccumulator[N <: Arity, T, R](val comp: R) {

  private val underlying = scala.collection.mutable
    .Map[Constructor[N], (Seq[Variable[Ind]], T)]()

  def +=(cons: Constructor[N], value: (Seq[Variable[Ind]], T)) = underlying +=
    (cons -> value)

  def isValid(adt: ADT[N]): Option[String] =
    val constructors = adt.constructors.toSet
    val casesConstructors = underlying.keySet.toSet

    val constructorsMinusCases = constructors -- casesConstructors
    val casesMinusConstructors = casesConstructors -- constructors

    if !constructorsMinusCases.isEmpty then
      Some(s"Case for ${constructorsMinusCases.head.name} is missing.")
    else if !casesMinusConstructors.isEmpty then
      Some(s"${casesMinusConstructors.head.name} is not a constructor of ${adt.name}.")
    else
      underlying.keys.foldLeft[Option[String]](None)((acc, c) =>
        val vars = underlying(c)._1.toSet
        acc.orElse(
          Some(s"Case ${c.name}: ${vars
              .size} variables were provided whereas the arity of ${c.name} is ${c
              .arity}.").filter(_ => vars.size != c.semantic.arity)
        )
      )

  def build: Map[Constructor[N], (Seq[Variable[Ind]], T)] = underlying.toMap
}

@deprecated("Use CaseAccumulator", "ADTv2")
type CaseBuilder[N <: Arity, T, R] = CaseAccumulator[N, T, R]
