package lisa.fol

import lisa.fol.FOL.*
import lisa.kernel.fol.FOL.Identifier
import lisa.utils.LisaException
import lisa.utils.K
/*
import lisa.kernel.proof.*
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.kernel.proof.SCProofCheckerJudgement.SCInvalidProof
import lisa.kernel.proof.SequentCalculus.*
 */
import lisa.utils.FOLParser

import scala.annotation.targetName
import scala.reflect.ClassTag

/**
 * A helper file that provides various syntactic sugars for LISA's FOL and proofs. Best imported through utilities.Helpers
 * Usage:
 * <pre>
 * import utilities.Helpers.*
 * </pre>
 * or
 * <pre>
 * extends utilities.KernelHelpers.*
 * </pre>
 */
object FOLHelpers {
  export lisa.utils.KernelHelpers.{freshId, nFreshId, given_Conversion_String_Identifier, given_Conversion_Identifier_String, given_Conversion_Boolean_List_String_Option}

  /////////////////
  // FOL helpers //
  /////////////////

  /* Conversions */
  //Conversions to lambdaExpression's
  given[T <: LisaObject[T], R <: LisaObject[R]]: Conversion[R, LambdaExpression[T, R, 0]] = LambdaExpression[T, R, 0](Seq(), _, 0)
  given[T <: LisaObject[T], R <: LisaObject[R]]: Conversion[(SchematicLabel[T], R), LambdaExpression[T, R, 1]] = a => LambdaExpression(Seq(a._1), a._2, 1)
  given[T <: LisaObject[T],R <: LisaObject[R], N <: Arity]: Conversion[(SchematicLabel[T]**N, R), LambdaExpression[T, R, N]] = a => {
    val s = a._1.toSeq
    LambdaExpression(s, a._2, s.length.asInstanceOf)
  }


  //helpers to create new schematic symbols, fetching the scala name of the variable.
  def variable(using name: sourcecode.Name): Variable = Variable(name.value)
  def function[N <: Arity : ValueOf](using name: sourcecode.Name): SchematicFunctionalLabel[N] = SchematicFunctionalLabel[N](name.value, valueOf[N])
  def formulaVariable(using name: sourcecode.Name): VariableFormula = VariableFormula(name.value)
  def predicate[N <: Arity : ValueOf](using name: sourcecode.Name): SchematicPredicateLabel[N] = SchematicPredicateLabel[N](name.value, valueOf[N])
  def connector[N <: Arity : ValueOf](using name: sourcecode.Name): SchematicConnectorLabel[N] = SchematicConnectorLabel[N](name.value, valueOf[N])








  //All commented

/*
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

  private def any2set[A, T <: A](any: T)(using c: FormulaSetConverter[T]): Set[Formula] = c.apply(any)

  extension [A, T1 <: A](left: T1)(using FormulaSetConverter[T1]) {
    infix def |-[B, T2 <: B](right: T2)(using FormulaSetConverter[T2]): Sequent = Sequent(any2set(left), any2set(right))
    infix def ⊢[B, T2 <: B](right: T2)(using FormulaSetConverter[T2]): Sequent = Sequent(any2set(left), any2set(right))
  }

  */
/*
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

 */


  /*
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
*/

  //////////////////////////////
  //  Conversion From Kernel  //
  //////////////////////////////
  

/*
def termFromKernel(t:K.Term) =
  t.label match {
  case K.ConstantFunctionLabel(id, arity) => if (arity==0) Constant(id) else ConstantFunctionalLabel(id).apply(t.args.map(termFromKernel))
  case lab: K.SchematicTermLabel => lab match {
    case SchematicFunctionLabel(id, arity) => if (arity==0) Variable(id) else ConstantFunctionalLabel(id).apply(t.args.map(termFromKernel))
    case VariableLabel(id) => ???
  }
}
*/
//args.map(termFromKernel)







/*


  /////////////////////////////
  // RunningTheories Helpers //
  /////////////////////////////

  extension (theory: RunningTheory) {
    def makeAxiom(using name: sourcecode.Name)(formula: Formula): theory.Axiom = theory.addAxiom(name.value, formula) match {
      case Some(value) => value
      case None => throw new LisaException.InvalidAxiomException("Axiom contains undefined symbols", name.value, formula, theory)
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
      case thm: RunningTheory#Theorem => s" Theorem ${thm.name} := ${FOLPrinter.prettySequent(thm.proposition)}\n"
      case axiom: RunningTheory#Axiom => s" Axiom ${axiom.name} := ${FOLPrinter.prettyFormula(axiom.ax)}\n"
      case d: RunningTheory#Definition =>
        d match {
          case pd: RunningTheory#PredicateDefinition =>
            s" Definition of predicate symbol ${pd.label.id} := ${FOLPrinter.prettyFormula(pd.label(pd.expression.vars.map(VariableTerm.apply)*) <=> pd.expression.body)}\n"
          case fd: RunningTheory#FunctionDefinition =>
            s" Definition of function symbol ${FOLPrinter.prettyTerm(fd.label(fd.expression.vars.map(VariableTerm.apply)*))} := the ${fd.out.id} such that ${FOLPrinter
                .prettyFormula((fd.out === fd.label(fd.expression.vars.map(VariableTerm.apply)*)) <=> fd.expression.body)})\n"
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


 */

}
