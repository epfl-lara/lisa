package lisa.utilcfs

object K {
  export lisa.kernelcf.fol.FOL.*
  import lisa.kernelcf.proof as P

  type Sequent = P.Sequent
  val Sequent = P.Sequent
  type Theory = P.Theory
  val Theory = P.Theory
  type MutableTheory = P.MutableTheory
  type Thm = P.Thm
  type ProofError = P.ProofError
  type GeneralError = P.GeneralError
  type SortMismatch = P.SortMismatch
  val SortMismatch = P.SortMismatch
  type TheoryMismatch = P.TheoryMismatch
  val TheoryMismatch = P.TheoryMismatch
  type Step = P.Step

  val Helpers = P.Helpers
  val Sorry = P.Sorry
  val Axiom = P.Axiom
  val Definition = P.Definition
  val Restate = P.Restate
  val RestateTrue = P.RestateTrue
  val Hypothesis = P.Hypothesis
  val Cut = P.Cut
  val LeftAnd = P.LeftAnd
  val LeftOr = P.LeftOr
  val LeftImplies = P.LeftImplies
  val LeftIff = P.LeftIff
  val LeftNot = P.LeftNot
  val LeftForall = P.LeftForall
  val LeftExists = P.LeftExists
  val RightAnd = P.RightAnd
  val RightOr = P.RightOr
  val RightImplies = P.RightImplies
  val RightIff = P.RightIff
  val RightNot = P.RightNot
  val RightForall = P.RightForall
  val RightExists = P.RightExists
  val RightEpsilon = P.RightEpsilon
  val Weakening = P.Weakening
  val LeftRefl = P.LeftRefl
  val RightRefl = P.RightRefl
  val LeftSubstEq = P.LeftSubstEq
  val RightSubstEq = P.RightSubstEq
  val InstSchema = P.InstSchema

  def sequentToFormula(s: Sequent): Expression = P.sequentToFormula(s)
  def isSameSequent(l: Sequent, r: Sequent): Boolean = P.isSameSequent(l, r)
  def isImplyingSequent(l: Sequent, r: Sequent): Boolean = P.isImplyingSequent(l, r)

  given Conversion[String, Identifier] = Identifier(_)
  given Conversion[Identifier, String] = _.toString

  def freshId(taken: Iterable[Identifier], base: Identifier): Identifier =
    val baseName = base.name
    Identifier(
      baseName,
      (Iterator.single(base.no) ++ taken.iterator.collect { case Identifier(`baseName`, no) => no }).max + 1
    )

  def freshId(taken: Iterable[Identifier], base: String): Identifier =
    freshId(taken, Identifier(base))
}
