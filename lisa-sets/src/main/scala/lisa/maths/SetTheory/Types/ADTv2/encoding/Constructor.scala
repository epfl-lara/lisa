package lisa.maths.SetTheory.Types.ADTv2.encoding

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Functions.Predef.*
import lisa.maths.SetTheory.Types.TypingHelpers.{FunctionalClass, TypedConstantFunctional, *}
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.funEqDef
import lisa.utils.prooflib.ProofTacticLib.Arity

/**
 *  Type theoretic interpretation of a constructor, that is a function whose type is
 *
 *  `c :: ∀X1, ..., Xn. T1 -> ... -> Tn -> ADT
 *
 *  @tparam N the number of type variables appearing in the definition of this
 *    constructor's ADT
 *  @param line the line at which this constructor is defined. Usually fetched
 *    automatically by the compiler. Used for error reporting
 *  @param file the file  in which this constructor is defined. Usually fetched
 *    automatically by the compiler. Used for error reporting
 *  @param semantic the set theoretic semantic constructor
 */
// class Constructor[N <: Arity] private[ADTv2] (using
class Constructor[N <: Arity]  (using
    line: sourcecode.Line,
    file: sourcecode.File
)(private[ADTv2] val semantic: SemanticConstructor[N])
    extends TypedConstantFunctional[Ind](
      semantic.fullName,
      FunctionalClass(
        // List.fill(semantic.typeArity)(None),
        // semantic.typeVariablesSeq.toList,
        Nil,
        Nil,
        semantic.typ
      ),
      semantic.intro
    ) {

  /**
   *  Name of the constructor
   *
   *  e.g `list/cons` or `list/nil`
   */
  val name = semantic.fullName

  val debug_semantic: SemanticConstructor[N] = semantic

  /**
   *  Theorem --- Introduction rule
   *
   *  `c :: ∀X1, ..., Xn. T1 -> ... -> Tn -> ADT
   *
   *  where `c` is this constructor, `ADT` the ADT it belongs to and `T1, ..., Tn` the
   *  domains of the constructor's arguments. X1, ..., Xn are the type variables of the
   *  ADT.
   */
  val intro = THM(
    semantic.intro.statement,
    s"${name}/introduction",
    line.value,
    file.value,
    Theorem
  )(have(semantic.intro))

  /**
   *  Theorem --- Introduction rule for this constructor.
   *
   *  `x1 ∈ T1(X1, ..., Xm), ..., xn ∈ Tn(X1, ..., Xm) ⊢ c(X1, ..., Xm) * x1 * ... * xn ∈ ADT(X1, ..., Xm)`
   *
   *  where Xi are the (schematic) type variables of the ADT and Ti are domains of this
   *  constructor's arguments.
   *
   *  e.g. `⊢ nil(T) ∈ list(T)` and `head ∈ T, tail ∈ list(T) ⊢ cons(T)(head)(tail) ∈ list(T)`
   */
  val introApp = Theorem(using name = sourcecode.FullName(s"${name}/introApp"))(
    wellTypedSet(semantic.semanticSignature) |-
      (semantic.appliedTerm :: semantic.adt.term)
  ) {

    have(semantic.intro.statement) by Restate.from(intro)

    // Instantiate possible type-parameter quantifiers in intro.
    val introInstantiated = semantic.typeVariablesSeq.foldLeft(lastStep)((fact, v) =>
      fact.statement.right.head match
        case forall(_, phi) => thenHave(phi) by InstantiateForall(v)
        case _ => fact
    )

    // Build c(x1)...(xn) typing from c :: T1 ->: ... ->: Tn ->: ADT using foldLeft.
    val (finalFact, _, _) = semantic.variables.foldLeft(
      (introInstantiated, semantic.term(semantic.typeVariablesSeq): Expr[Ind], semantic.typ: Expr[Ind])
    ) { case ((accFact, accTerm, accType), v) =>
      accType match
        case aTy ->: bTy =>
          val vTyped = assume(v :: aTy)
          val nextFact = have(accTerm * v :: bTy) by Tautology.from(
            accFact,
            funEqDef of (f := accTerm, a := aTy, b := bTy, x := v),
            vTyped
          )
          (nextFact, accTerm * v, bTy)
        case _ => throw UnreachableException
    }

    have(thesis) by Tautology.from(finalFact)
  }

  /**
   *  Theorem --- Injectivity
   *
   *  ` c(x1, ..., xn) = c(y1, ..., yn) <=> x1 = y1 /\ ... /\ xn = yn`
   */
  lazy val injectivity = THM(
    semantic.injectivity.statement,
    s"${name}/injectivity",
    line.value,
    file.value,
    Theorem
  )(have(semantic.injectivity))

  /** Type variables appearing in the signature of this constructor */
  val typeVariables: Variable[Ind] ** N = semantic.typeVariables

  /**
   *  Instantiate constructor type parameters with expression-level type arguments.
   *
   *  Empty arguments keep schematic type variables (for debug/printing consistency).
   */
  def apply(args: Expr[Ind]*): Expr[Ind] = {
    val expected = typeVariables.toSeq.size
    require(
      args.size == expected || args.isEmpty,
      s"Constructor $name expects $expected type argument(s), got ${args.size}."
    )
    if args.isEmpty then semantic.term(semantic.typeVariablesSeq)
    else semantic.term(args)
  }

  /** Backward-compatible alias for constructor specialization. */
  def of(args: Expr[Ind]*): Expr[Ind] = apply(args*)
}
