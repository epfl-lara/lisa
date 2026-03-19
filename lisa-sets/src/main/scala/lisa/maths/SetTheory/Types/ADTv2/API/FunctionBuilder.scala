package lisa.maths.SetTheory.Types.ADTv2.API

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.encoding.ADT
import lisa.maths.SetTheory.Types.ADTv2.encoding.Constructor
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticADT
import lisa.maths.SetTheory.Types.ADTv2.encoding.Utils.{appSeq, wellTypedSet}
import lisa.maths.SetTheory.Types.ADTv2.functions.*

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity

case class Case[N <: Arity](cons: Constructor[N], vars: Variable[Ind]*) {

  /**
   *  Used in the context of an induction proof. Adds the subproof corresponding to this
   *  case into a builder.
   *
   *  @see [[Induction]]
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
      builder: CaseBuilder[N, proof.ProofStep, (Sequent, Seq[Expr[Ind]], Variable[Ind])]
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

    // val botWithAssumptions = bot.substitute(subst) ++ ((assumptions ++ proof.getAssumptions) |- ())
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
  def apply(body: Expr[Ind])(using builder: CaseBuilder[N, Expr[Ind], Unit]) = builder +=
    (cons, (vars, body))
}

class CaseBuilder[N <: Arity, T, R](val comp: R) {

  /**
   *  The underlying mutable map between patterns and the body of the corresponding cases.
   *  For each patterns stores the variables that have been used to represent its
   *  arguments.
   */
  private val underlying = scala.collection.mutable
    .Map[Constructor[N], (Seq[Variable[Ind]], T)]()

  /**
   *  Adds a case to the pattern matching
   *
   *  @param cons the pattern / constructor
   *  @param value the value next to the variables that are used for the pattern's
   *    arguments
   */
  def +=(cons: Constructor[N], value: (Seq[Variable[Ind]], T)) = underlying +=
    (cons -> value)

  /**
   *  Checks if the cases of a pattern matching are valid. Specifically, it checks that:
   *    - All constructors are covered
   *    - There are no extra cases
   *    - The number of variables provided by the user matches the arity of the
   *      constructor
   *
   *  @param adt the ADT over which the pattern matching is performed
   *  @return an error message if the pattern matching is invalid, None otherwise
   */
  def isValid(adt: ADT[N]): Option[String] =
    val constructors = adt.constructors.toSet
    val casesConstructors = underlying.keySet.toSet

    val constructorsMinusCases = constructors -- casesConstructors
    val casesMinusConstructors = casesConstructors -- constructors

    // STEP 1: Check that all constructors are covered
    if !constructorsMinusCases.isEmpty then
      Some(s"Case for ${constructorsMinusCases.head.name} is missing.")
    // STEP 2: Check that there are no extra cases
    else if !casesMinusConstructors.isEmpty then
      Some(s"${casesMinusConstructors.head.name} is not a constructor of ${adt.name}.")
    else
      underlying.keys.foldLeft[Option[String]](None)((acc, c) =>
        val vars = underlying(c)._1.toSet
        // STEP 3: Check that for each case the number of variables provided by the user matches the arity of the constructor
        acc.orElse(
          Some(s"Case ${c.name}: ${vars
              .size} variables were provided whereas the arity of ${c.name} is ${c
              .arity}.").filter(_ => vars.size != c.semantic.arity)
        )
      )

  /** Outputs an immutable map out of the underlying mutable one */
  def build: Map[Constructor[N], (Seq[Variable[Ind]], T)] = underlying.toMap
}

def fun[N <: Arity](adt: ADT[N], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(cases: CaseBuilder[N, Expr[Ind], Unit] ?=> Unit): ADTFunction[N] = {
  val builder = CaseBuilder[N, Expr[Ind], Unit](())
  cases(using builder)
  builder.isValid(adt) match
    case None => ADTFunction(
        SemanticFunction[N](
          name.value,
          adt.semantic,
          builder.build.map((k, v) => (k.semantic, v)),
          returnType
        ),
        adt
      )
    case Some(msg) => throw new IllegalArgumentException(msg)
}
