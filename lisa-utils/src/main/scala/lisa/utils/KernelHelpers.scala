package lisa.utils

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.kernel.proof.SCProofCheckerJudgement.SCInvalidProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.proof.*
import lisa.utils.FOLParser

import scala.annotation.targetName

/**
 * A helper file that provides various syntactic sugars for LISA's FOL and proofs at the Kernel level.
 */
object KernelHelpers {

  /////////////////
  // FOL helpers //
  /////////////////

  /* Prefix syntax */

  val === = equality
  val ⊤ : Formula = top()
  val ⊥ : Formula = bot()
  val True: Formula = top()
  val False: Formula = bot()

  val neg = Neg
  val ¬ = neg
  val ! = neg
  val and = And
  val /\ = And
  val or = Or
  val \/ = Or
  val implies = Implies
  val ==> = Implies
  val iff = Iff
  val <=> = Iff
  val forall = Forall
  val ∀ = forall
  val exists = Exists
  val ∃ = exists
  val existsOne = ExistsOne
  val ∃! = existsOne

  extension [L <: TermLabel](label: L) {
    def apply(args: Term*): Term = Term(label, args)
    @targetName("applySeq")
    def apply(args: Seq[Term]): Term = Term(label, args)
    def unapply(f: Formula): Option[Seq[Formula]] = f match {
      case ConnectorFormula(`label`, args) => Some(args)
      case _ => None
    }
  }

  extension [L <: PredicateLabel](label: L) {
    def apply(args: Term*): Formula = PredicateFormula(label, args)
    @targetName("applySeq")
    def apply(args: Seq[Term]): Formula = PredicateFormula(label, args)
    def unapply(f: Formula): Option[Seq[Term]] = f match {
      case PredicateFormula(`label`, args) => Some(args)
      case _ => None
    }
  }

  extension [L <: ConnectorLabel](label: L) {
    def apply(args: Formula*): Formula = ConnectorFormula(label, args)
    @targetName("applySeq")
    def apply(args: Seq[Formula]): Formula = ConnectorFormula(label, args)
    def unapply(f: Formula): Option[Seq[Formula]] = f match {
      case ConnectorFormula(`label`, args) => Some(args)
      case _ => None
    }
  }

  extension [L <: BinderLabel](label: L) {
    def apply(bound: VariableLabel, inner: Formula): Formula = BinderFormula(label, bound, inner)
    def unapply(f: Formula): Option[(VariableLabel, Formula)] = f match {
      case BinderFormula(`label`, x, inner) => Some((x, inner))
      case _ => None
    }
  }

  /* Infix syntax */

  extension (f: Formula) {
    def unary_! = ConnectorFormula(Neg, Seq(f))
    infix inline def ==>(g: Formula): Formula = ConnectorFormula(Implies, Seq(f, g))
    infix inline def <=>(g: Formula): Formula = ConnectorFormula(Iff, Seq(f, g))
    infix inline def /\(g: Formula): Formula = ConnectorFormula(And, Seq(f, g))
    infix inline def \/(g: Formula): Formula = ConnectorFormula(Or, Seq(f, g))
  }

  extension (t: Term) {
    infix def ===(u: Term): Formula = PredicateFormula(equality, Seq(t, u))
    infix def ＝(u: Term): Formula = PredicateFormula(equality, Seq(t, u))
  }

  /* Conversions */

  given Conversion[TermLabel, Term] = Term(_, Seq())
  given Conversion[Term, TermLabel] = _.label
  given Conversion[PredicateLabel, PredicateFormula] = PredicateFormula(_, Seq())
  given Conversion[PredicateFormula, PredicateLabel] = _.label

  given Conversion[VariableFormulaLabel, PredicateFormula] = PredicateFormula(_, Seq())
  given Conversion[(Boolean, List[Int], String), Option[(List[Int], String)]] = tr => if (tr._1) None else Some(tr._2, tr._3)
  given Conversion[Formula, Sequent] = () |- _

  /* Sequents */

  val emptySeq: Sequent = Sequent(Set.empty, Set.empty)

  extension (s: Sequent) {
    // non OL-based / naive Sequent manipulation
    infix def +<<(f: Formula): Sequent = s.copy(left = s.left + f)
    infix def -<<(f: Formula): Sequent = s.copy(left = s.left - f)
    infix def +>>(f: Formula): Sequent = s.copy(right = s.right + f)
    infix def ->>(f: Formula): Sequent = s.copy(right = s.right - f)
    infix def ++<<(s1: Sequent): Sequent = s.copy(left = s.left ++ s1.left)
    infix def --<<(s1: Sequent): Sequent = s.copy(left = s.left -- s1.left)
    infix def ++>>(s1: Sequent): Sequent = s.copy(right = s.right ++ s1.right)
    infix def -->>(s1: Sequent): Sequent = s.copy(right = s.right -- s1.right)
    infix def ++(s1: Sequent): Sequent = s.copy(left = s.left ++ s1.left, right = s.right ++ s1.right)
    infix def --(s1: Sequent): Sequent = s.copy(left = s.left -- s1.left, right = s.right -- s1.right)

    // OL-based Sequent manipulation
    infix def removeLeft(f: Formula): Sequent = s.copy(left = s.left.filterNot(isSame(_, f)))
    infix def removeRight(f: Formula): Sequent = s.copy(right = s.right.filterNot(isSame(_, f)))
    infix def removeAllLeft(s1: Sequent): Sequent = s.copy(left = s.left.filterNot(e1 => s1.left.exists(e2 => isSame(e1, e2))))
    infix def removeAllLeft(s1: Set[Formula]): Sequent = s.copy(left = s.left.filterNot(e1 => s1.exists(e2 => isSame(e1, e2))))
    infix def removeAllRight(s1: Sequent): Sequent = s.copy(right = s.right.filterNot(e1 => s1.right.exists(e2 => isSame(e1, e2))))
    infix def removeAllRight(s1: Set[Formula]): Sequent = s.copy(right = s.right.filterNot(e1 => s1.exists(e2 => isSame(e1, e2))))
    infix def removeAll(s1: Sequent): Sequent = s.copy(left = s.left.filterNot(e1 => s1.left.exists(e2 => isSame(e1, e2))), right = s.right.filterNot(e1 => s1.right.exists(e2 => isSame(e1, e2))))

    infix def addLeftIfNotExists(f: Formula): Sequent = if (s.left.exists(isSame(_, f))) s else (s +<< f)
    infix def addRightIfNotExists(f: Formula): Sequent = if (s.right.exists(isSame(_, f))) s else (s +>> f)
    infix def addAllLeftIfNotExists(s1: Sequent): Sequent = s ++<< s1.copy(left = s1.left.filterNot(e1 => s.left.exists(isSame(_, e1))))
    infix def addAllRightIfNotExists(s1: Sequent): Sequent = s ++>> s1.copy(right = s1.right.filterNot(e1 => s.right.exists(isSame(_, e1))))
    infix def addAllIfNotExists(s1: Sequent): Sequent = s ++ s1.copy(left = s1.left.filterNot(e1 => s.left.exists(isSame(_, e1))), right = s1.right.filterNot(e1 => s.right.exists(isSame(_, e1))))

    // OL shorthands
    infix def +<?(f: Formula): Sequent = s addLeftIfNotExists f
    infix def -<?(f: Formula): Sequent = s removeLeft f
    infix def +>?(f: Formula): Sequent = s addRightIfNotExists f
    infix def ->?(f: Formula): Sequent = s removeRight f
    infix def ++<?(s1: Sequent): Sequent = s addAllLeftIfNotExists s1
    infix def --<?(s1: Sequent): Sequent = s removeAllLeft s1
    infix def ++>?(s1: Sequent): Sequent = s addAllRightIfNotExists s1
    infix def -->?(s1: Sequent): Sequent = s removeAllRight s1
    infix def --?(s1: Sequent): Sequent = s removeAll s1
    infix def ++?(s1: Sequent): Sequent = s addAllIfNotExists s1
  }

  // TODO: Should make less generic
  /**
   * Represents a converter of some object into a set.
   * @tparam S The type of elements in that set
   * @tparam T The type to convert from
   */
  protected trait FormulaSetConverter[T] {
    def apply(t: T): Set[Formula]
  }

  given FormulaSetConverter[Unit] with {
    override def apply(u: Unit): Set[Formula] = Set.empty
  }

  given FormulaSetConverter[EmptyTuple] with {
    override def apply(t: EmptyTuple): Set[Formula] = Set.empty
  }

  given [H <: Formula, T <: Tuple](using c: FormulaSetConverter[T]): FormulaSetConverter[H *: T] with {
    override def apply(t: H *: T): Set[Formula] = c.apply(t.tail) + t.head
  }

  given formula_to_set[T <: Formula]: FormulaSetConverter[T] with {
    override def apply(f: T): Set[Formula] = Set(f)
  }

  given [T <: Formula, I <: Iterable[T]]: FormulaSetConverter[I] with {
    override def apply(s: I): Set[Formula] = s.toSet
  }

  given FormulaSetConverter[VariableFormulaLabel] with {
    override def apply(s: VariableFormulaLabel): Set[Formula] = Set(s())
  }

  private def any2set[A, T <: A](any: T)(using c: FormulaSetConverter[T]): Set[Formula] = c.apply(any)

  extension [A, T1 <: A](left: T1)(using FormulaSetConverter[T1]) {
    infix def |-[B, T2 <: B](right: T2)(using FormulaSetConverter[T2]): Sequent = Sequent(any2set(left), any2set(right))
    infix def ⊢[B, T2 <: B](right: T2)(using FormulaSetConverter[T2]): Sequent = Sequent(any2set(left), any2set(right))
  }

  // Instatiation functions for formulas lifted to sequents.

  def instantiatePredicateSchemaInSequent(s: Sequent, m: Map[SchematicVarOrPredLabel, LambdaTermFormula]): Sequent = {
    s.left.map(phi => instantiatePredicateSchemas(phi, m)) |- s.right.map(phi => instantiatePredicateSchemas(phi, m))
  }

  def instantiateFunctionSchemaInSequent(s: Sequent, m: Map[SchematicTermLabel, LambdaTermTerm]): Sequent = {
    s.left.map(phi => instantiateTermSchemas(phi, m)) |- s.right.map(phi => instantiateTermSchemas(phi, m))
  }

  def instantiateSchemaInSequent(
      s: Sequent,
      mCon: Map[SchematicConnectorLabel, LambdaFormulaFormula],
      mPred: Map[SchematicVarOrPredLabel, LambdaTermFormula],
      mTerm: Map[SchematicTermLabel, LambdaTermTerm]
  ): Sequent = {
    s.left.map(phi => instantiateSchemas(phi, mCon, mPred, mTerm)) |- s.right.map(phi => instantiateSchemas(phi, mCon, mPred, mTerm))
  }

  //////////////////////
  // SCProofs helpers //
  //////////////////////
  extension (sp: SCSubproof) {

    /**
     * Explore a proof with a specific path and returns the pointed proofstep.
     * @param path A path through subproofs of a proof.
     */
    def followPath(path: Seq[Int]): SCProofStep = path match {
      case Nil => sp
      case n :: Nil => sp.sp(n)
      case n :: ns =>
        assert(sp.sp.steps(n).isInstanceOf[SCSubproof], s"Got $path but next step is not a subproof: ${sp.sp.steps(n).getClass}")
        sp.sp.steps(n).asInstanceOf[SCSubproof].followPath(ns)
    }
  }

  extension (p: SCProof) {

    /**
     * Explore a proof with a specific path and returns the pointed proofstep.
     * @param path A path through subproofs of a proof.
     */
    def followPath(path: Seq[Int]): SCProofStep = SCSubproof(p, p.imports.indices).followPath(path)
  }

  // Conversions from String to datatypes
  // given Conversion[String, Sequent] = FOLParser.parseSequent(_)
  // given Conversion[String, Formula] = FOLParser.parseFormula(_)
  // given Conversion[String, Term] = FOLParser.parseTerm(_)
  // given Conversion[String, VariableLabel] = s => VariableLabel(if (s.head == '?') s.tail else s)

  // Conversion from pairs (e.g. x -> f(x)) to lambdas
  given Conversion[Term, LambdaTermTerm] = LambdaTermTerm(Seq(), _)
  given Conversion[VariableLabel, LambdaTermTerm] = a => LambdaTermTerm(Seq(), a: Term)
  given Conversion[(VariableLabel, Term), LambdaTermTerm] = a => LambdaTermTerm(Seq(a._1), a._2)
  given Conversion[(Seq[VariableLabel], Term), LambdaTermTerm] = a => LambdaTermTerm(a._1, a._2)

  given Conversion[Formula, LambdaTermFormula] = LambdaTermFormula(Seq(), _)
  given Conversion[(VariableLabel, Formula), LambdaTermFormula] = a => LambdaTermFormula(Seq(a._1), a._2)
  given Conversion[(Seq[VariableLabel], Formula), LambdaTermFormula] = a => LambdaTermFormula(a._1, a._2)

  given Conversion[Formula, LambdaFormulaFormula] = LambdaFormulaFormula(Seq(), _)
  given Conversion[(VariableFormulaLabel, Formula), LambdaFormulaFormula] = a => LambdaFormulaFormula(Seq(a._1), a._2)
  given Conversion[(Seq[VariableFormulaLabel], Formula), LambdaFormulaFormula] = a => LambdaFormulaFormula(a._1, a._2)

  // Shortcut for LambdaTermTerm, LambdaTermFormula and LambdaFormulaFormula construction
  def lambda(x: VariableLabel, t: Term): LambdaTermTerm = LambdaTermTerm(Seq(x), t)
  def lambda(xs: Seq[VariableLabel], t: Term): LambdaTermTerm = LambdaTermTerm(xs, t)
  def lambda(x: VariableLabel, l: LambdaTermTerm): LambdaTermTerm = LambdaTermTerm(Seq(x) ++ l.vars, l.body)
  def lambda(xs: Seq[VariableLabel], l: LambdaTermTerm): LambdaTermTerm = LambdaTermTerm(xs ++ l.vars, l.body)

  def lambda(x: VariableLabel, phi: Formula): LambdaTermFormula = LambdaTermFormula(Seq(x), phi)
  def lambda(xs: Seq[VariableLabel], phi: Formula): LambdaTermFormula = LambdaTermFormula(xs, phi)
  def lambda(x: VariableLabel, l: LambdaTermFormula): LambdaTermFormula = LambdaTermFormula(Seq(x) ++ l.vars, l.body)
  def lambda(xs: Seq[VariableLabel], l: LambdaTermFormula): LambdaTermFormula = LambdaTermFormula(xs ++ l.vars, l.body)

  def lambda(X: VariableFormulaLabel, phi: Formula): LambdaFormulaFormula = LambdaFormulaFormula(Seq(X), phi)
  def lambda(Xs: Seq[VariableFormulaLabel], phi: Formula): LambdaFormulaFormula = LambdaFormulaFormula(Xs, phi)
  def lambda(X: VariableFormulaLabel, l: LambdaFormulaFormula): LambdaFormulaFormula = LambdaFormulaFormula(Seq(X) ++ l.vars, l.body)
  def lambda(Xs: Seq[VariableFormulaLabel], l: LambdaFormulaFormula): LambdaFormulaFormula = LambdaFormulaFormula(Xs ++ l.vars, l.body)

  def instantiateBinder(f: BinderFormula, t: Term): Formula = substituteVariablesInFormula(f.inner, Map(f.bound -> t))

  // declare symbols easily: "val x = variable;"
  def variable(using name: sourcecode.Name): VariableLabel = VariableLabel(name.value)
  def function(arity: Integer)(using name: sourcecode.Name): SchematicFunctionLabel = SchematicFunctionLabel(name.value, arity)
  def formulaVariable(using name: sourcecode.Name): VariableFormulaLabel = VariableFormulaLabel(name.value)
  def predicate(arity: Integer)(using name: sourcecode.Name): SchematicPredicateLabel = SchematicPredicateLabel(name.value, arity)
  def connector(arity: Integer)(using name: sourcecode.Name): SchematicConnectorLabel = SchematicConnectorLabel(name.value, arity)

  // Conversions from String to Identifier
  class InvalidIdentifierException(identifier: String, errorMessage: String) extends LisaException(errorMessage) {
    def showError: String = errorMessage
  }

  given Conversion[String, Identifier] = str => {
    val pieces = str.split(Identifier.counterSeparator)
    if (pieces.length == 1) {
      val name = pieces.head
      if (!Identifier.isValidIdentifier(name)) {
        val no: String = Identifier.forbiddenChars.mkString("")
        throw new InvalidIdentifierException(str, s"Identifier must not contain whitespaces nor symbols among $no.")
      }
      Identifier(name)
    } else if (pieces.length == 2) {
      val name = pieces.head
      val no = pieces(1)
      if (!no.forall(_.isDigit) || no.isEmpty || (no.length > 1 && no.head == '0')) {
        throw new InvalidIdentifierException(str, s"The part of an identifier contained after ${Identifier.counterSeparator} must be a number without leading 0s.")
      }
      if (!Identifier.isValidIdentifier(name)) {
        val no: String = Identifier.forbiddenChars.mkString("")
        throw new InvalidIdentifierException(str, s"Identifier must not contain whitespaces nor symbols among $no.")
      }
      Identifier(name, no.toInt)
    } else { // if number of _ is greater than 1
      throw new InvalidIdentifierException("name", s"The identifier cannot contain more than one counter separator (${Identifier.counterSeparator}).")
    }
  }
  given Conversion[Identifier, String] = _.toString

  // Generates  new Identifier from an existing list
  def freshId(taken: Iterable[Identifier], base: Identifier): Identifier = {
    new Identifier(
      base.name,
      (taken.collect({ case Identifier(base.name, no) =>
        no
      }) ++ Iterable(base.no)).max + 1
    )
  }

  def nFreshId(taken: Iterable[Identifier], n: Int): IndexedSeq[Identifier] = {
    val max = if (taken.isEmpty) 0 else taken.map(c => c.no).max
    Range(0, n).map(i => Identifier("gen", max + i))
  }

  /////////////////////////////
  // RunningTheories Helpers //
  /////////////////////////////

  extension (theory: RunningTheory) {
    def makeAxiom(using name: sourcecode.Name)(formula: Formula): theory.Axiom = theory.addAxiom(name.value, formula) match {
      case Some(value) => value
      case None => throw new LisaException.InvalidKernelAxiomException("Axiom contains undefined symbols", name.value, formula, theory)
    }

    /**
     * Add a theorem to the theory, but also asks explicitely for the desired conclusion
     * of the theorem to have more explicit writing and for sanity check.
     */
    def theorem(name: String, statement: Sequent, proof: SCProof, justifications: Seq[theory.Justification]): RunningTheoryJudgement[theory.Theorem] = {
      if (statement == proof.conclusion) theory.makeTheorem(name, statement, proof, justifications)
      else if (isSameSequent(statement, proof.conclusion)) theory.makeTheorem(name, statement, proof.appended(Restate(statement, proof.length - 1)), justifications)
      else InvalidJustification(s"The proof proves ${FOLPrinter.prettySequent(proof.conclusion)} instead of claimed ${FOLPrinter.prettySequent(statement)}", None)
    }

    /**
     * Make a function definition in the theory, but only ask for the identifier of the new symbol; Arity is inferred
     * of the theorem to have more explicit writing and for sanity check. See [[lisa.kernel.proof.RunningTheory.makeFunctionDefinition]]
     */
    def functionDefinition(
        symbol: String,
        expression: LambdaTermFormula,
        out: VariableLabel,
        proof: SCProof,
        proven: Formula,
        justifications: Seq[theory.Justification]
    ): RunningTheoryJudgement[theory.FunctionDefinition] = {
      val label = ConstantFunctionLabel(symbol, expression.vars.size)
      theory.makeFunctionDefinition(proof, justifications, label, out, expression, proven)
    }

    /**
     * Make a predicate definition in the theory, but only ask for the identifier of the new symbol; Arity is inferred
     * of the theorem to have more explicit writing and for sanity check. See also [[lisa.kernel.proof.RunningTheory.makePredicateDefinition]]
     */
    def predicateDefinition(symbol: String, expression: LambdaTermFormula): RunningTheoryJudgement[theory.PredicateDefinition] = {
      val label = ConstantPredicateLabel(symbol, expression.vars.size)
      theory.makePredicateDefinition(label, expression)
    }

    /**
     * Try to fetch, in this order, a justification that is an Axiom with the given name,
     * a Theorem with a given name or a Definition with a the given name as symbol
     */
    def getJustification(name: String): Option[theory.Justification] = theory.getAxiom(name).orElse(theory.getTheorem(name)).orElse(theory.getDefinition(name))

    /**
     * Verify if a given formula belongs to some language
     *
     * @param phi The formula to check
     * @return The List of undefined symols
     */
    def findUndefinedSymbols(phi: Formula): Set[ConstantLabel] = phi match {
      case PredicateFormula(label, args) =>
        label match {
          case l: ConstantPredicateLabel => ((if (theory.isSymbol(l)) Nil else List(l)) ++ args.flatMap(findUndefinedSymbols)).toSet
          case _ => args.flatMap(findUndefinedSymbols).toSet
        }
      case ConnectorFormula(label, args) => args.flatMap(findUndefinedSymbols).toSet
      case BinderFormula(label, bound, inner) => findUndefinedSymbols(inner)
    }

    /**
     * Verify if a given term belongs to the language of the theory.
     *
     * @param t The term to check
     * @return The List of undefined symols
     */
    def findUndefinedSymbols(t: Term): Set[ConstantLabel] = t match {
      case Term(label, args) =>
        label match {
          case l: ConstantFunctionLabel => ((if (theory.isSymbol(l)) Nil else List(l)) ++ args.flatMap(findUndefinedSymbols)).toSet
          case _: SchematicTermLabel => args.flatMap(findUndefinedSymbols).toSet
        }

    }

    /**
     * Verify if a given sequent belongs to the language of the theory.
     *
     * @param s The sequent to check
     * @return The List of undefined symols
     */
    def findUndefinedSymbols(s: Sequent): Set[ConstantLabel] =
      s.left.flatMap(findUndefinedSymbols) ++ s.right.flatMap(findUndefinedSymbols)

  }

  extension (just: RunningTheory#Justification) {
    def repr: String = just match {
      case thm: RunningTheory#Theorem => s" Theorem ${thm.name} := ${FOLPrinter.prettySequent(thm.proposition)}${if (thm.withSorry) " (!! Relies on Sorry)" else ""}\n"
      case axiom: RunningTheory#Axiom => s" Axiom ${axiom.name} := ${FOLPrinter.prettyFormula(axiom.ax)}\n"
      case d: RunningTheory#Definition =>
        d match {
          case pd: RunningTheory#PredicateDefinition =>
            s" Definition of predicate symbol ${pd.label.id} := ${FOLPrinter.prettyFormula(pd.label(pd.expression.vars.map(VariableTerm.apply)*) <=> pd.expression.body)}\n"
          case fd: RunningTheory#FunctionDefinition =>
            s" Definition of function symbol ${FOLPrinter.prettyTerm(fd.label(fd.expression.vars.map(VariableTerm.apply)*))} := the ${fd.out.id} such that ${FOLPrinter
                .prettyFormula((fd.out === fd.label(fd.expression.vars.map(VariableTerm.apply)*)) <=> fd.expression.body)})${if (fd.withSorry) " (!! Relies on Sorry)" else ""}\n"
        }
    }
  }

  extension [J <: RunningTheory#Justification](theoryJudgement: RunningTheoryJudgement[J]) {

    /**
     * If the Judgement is valid, show the inner justification and returns it.
     * Otherwise, om.output the error leading to the invalid justification and throw an error.
     */
    def repr: String = {
      theoryJudgement match {
        case RunningTheoryJudgement.ValidJustification(just) =>
          just.repr
        case InvalidJustification(message, error) =>
          s"$message\n${error match {
              case Some(judgement) => FOLPrinter.prettySCProof(judgement)
              case None => ""
            }}"
      }
    }
  }

  /**
   * output a readable representation of a proof.
   */
  def checkProof(proof: SCProof, output: String => Unit = println): Unit = {
    val judgement = SCProofChecker.checkSCProof(proof)
    output(FOLPrinter.prettySCProof(judgement))
  }
}
