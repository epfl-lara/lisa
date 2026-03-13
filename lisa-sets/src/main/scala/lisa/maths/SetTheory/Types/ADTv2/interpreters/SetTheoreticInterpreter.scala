package lisa.maths.SetTheory.Types.ADTv2.interpreters

import lisa.maths.SetTheory.Types.ADTv2.backends.Backend
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.{ADTSpec, ConstructorSpec}

/** Set-theoretic interpreter for ADT v2 specs. */
object SetTheoreticInterpreter {

  /**
   * Semantic representation of an ADT with all set-theoretic artifacts.
   *
   * @param name ADT name (e.g., "list") - needed for user-facing API
   * @param typeParameters type parameter names (e.g., ["A"]) - needed for instantiation
   * @param typeSymbol the ADT type symbol (e.g., "list")
   * @param constructors map from constructor name to its semantic artifacts
   * @param inductionTheorem structural induction principle for the ADT
   * @param eliminationTheorem pattern matching/case analysis principle
   */
  final case class SemanticADT(
    name: String,
    typeParameters: Seq[String],
    typeSymbol: Backend#SymbolHandle,
    constructors: Map[String, SemanticConstructor],
    inductionTheorem: Backend#TheoremHandle,
    eliminationTheorem: Backend#TheoremHandle
  )

  /**
   * Semantic representation of a constructor with all theorems and auxiliary symbols.
   *
   * @param symbol the constructor symbol
   * @param introductionTheorem typing rule (e.g., cons :: A → list(A) → list(A))
   * @param injectivityTheorem equality preservation (cons x xs = cons y ys ⟺ x = y ∧ xs = ys)
   * @param disjointnessTheorems inequalities vs other constructors (nil ≠ cons x xs)
   * @param discriminator predicate testing for this constructor (is_cons)
   * @param selectors field extractors for constructor arguments (head, tail)
   */
  final case class SemanticConstructor(
    symbol: Backend#SymbolHandle,
    introductionTheorem: Backend#TheoremHandle,
    injectivityTheorem: Backend#TheoremHandle,
    disjointnessTheorems: Map[String, Backend#TheoremHandle],
    discriminator: Backend#SymbolHandle,
    selectors: Seq[Backend#SymbolHandle]
  )

  /**
   * Main entry point: interpret an ADT specification into semantic objects.
   *
   * This orchestrates the construction of all set-theoretic artifacts:
   * 1. Create constructor symbols with tagged-tuple encoding
   * 2. Generate theorems (introduction, injectivity, disjointness)
   * 3. Build ADT-level theorems (induction, elimination)
   * 4. Create auxiliary symbols (discriminators, selectors)
   *
   * Phase 3 note: For the vertical slice, this may initially delegate to
   * backend.defineADT and repackage results. Later iterations will use the
   * fine-grained helper methods below.
   *
   * @param spec the ADT specification from the syntax layer
   * @param backend the proof backend to use for creating definitions and theorems
   * @return semantic ADT with all theorems and symbols
   */
  def interpret(spec: ADTSpec, backend: Backend): SemanticADT = {

    val result = backend.defineADT(spec)

    SemanticADT(
      name = spec.name,
      typeParameters = spec.typeParameters,
      typeSymbol = backend.symbol(spec.name),
      constructors = spec.constructors.map { ctorSpec =>
        ctorSpec.name -> buildSemanticConstructor(spec, ctorSpec, backend)
      }.toMap,
      inductionTheorem = result.inductionTheorem,
      eliminationTheorem = ???
    )
  }

  private def buildSemanticConstructor(
    spec: ADTSpec,
    constructor: ConstructorSpec,
    backend: Backend
  ): SemanticConstructor = {
    val introThm = buildIntroduction(spec, constructor, backend)
    val injectivityThm = buildInjectivity(spec, constructor, backend)
    val disjointnessThms = spec.constructors.filterNot(_ == constructor).map { other =>
      other.name -> buildDisjointness(spec, constructor, other, backend)
    }.toMap
    val discriminator = buildDiscriminator(spec, constructor, backend)
    val selectors = buildSelectors(spec, constructor, backend)
    SemanticConstructor(
      symbol = backend.symbol(s"${spec.name}.${constructor.name}"),
      introductionTheorem = introThm,
      injectivityTheorem = injectivityThm,
      disjointnessTheorems = disjointnessThms,
      discriminator = discriminator,
      selectors = selectors
    )
  }

  // ---------------------------------------------------------------------------
  // Helper Methods for Building Semantic Artifacts
  // ---------------------------------------------------------------------------

  /**
   * Build the introduction (typing) theorem for a constructor.
   * Example: ∀ A. cons(A) :: A → list(A) → list(A)
   */
  def buildIntroduction(
    spec: ADTSpec,
    constructor: ConstructorSpec,
    backend: Backend
  ): Backend#TheoremHandle = {

    ???
  }

  /**
   * Build the injectivity theorem for a constructor.
   * Example: cons * x * xs = cons * y * ys ⟺ x = y ∧ xs = ys
   */
  private def buildInjectivity(
    spec: ADTSpec,
    constructor: ConstructorSpec,
    backend: Backend
  ): Backend#TheoremHandle = ???

  /**
   * Build disjointness theorem between two different constructors.
   * Example: nil(A) ≠ cons(A) * x * xs
   */
  private def buildDisjointness(
    spec: ADTSpec,
    constructor: ConstructorSpec,
    other: ConstructorSpec,
    backend: Backend
  ): Backend#TheoremHandle = ???

  /**
   * Build the structural induction theorem for the ADT.
   * Example for lists:
   * P(nil(A)) ⟹ (∀ x :: A. ∀ xs :: list(A). P(xs) ⟹ P(cons * x * xs)) ⟹ ∀ l :: list(A). P(l)
   */
  private def buildInduction(
    spec: ADTSpec,
    backend: Backend
  ): Backend#TheoremHandle = ???

  /**
   * Build the elimination (pattern matching) theorem for the ADT.
   * Example: ∀ x :: list(A). x = nil(A) ∨ (∃ h t. x = cons(A) * h * t)
   */
  private def buildElimination(
    spec: ADTSpec,
    backend: Backend
  ): Backend#TheoremHandle = ???

  /**
   * Build the discriminator predicate for a constructor.
   * Example: is_cons(l) ⟺ ∃ x xs. l = cons(A) * x * xs
   */
  private def buildDiscriminator(
    spec: ADTSpec,
    constructor: ConstructorSpec,
    backend: Backend
  ): Backend#SymbolHandle = ???

  /**
   * Build all selector functions for a constructor's arguments.
   * Example: for cons(head: A, tail: list), builds [head, tail]
   *          for node(value: B, left: tree, right: tree), builds [value, left, right]
   */
  private def buildSelectors(
    spec: ADTSpec,
    constructor: ConstructorSpec,
    backend: Backend
  ): Seq[Backend#SymbolHandle] = ???
}
