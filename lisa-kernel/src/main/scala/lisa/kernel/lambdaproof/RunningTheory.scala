package lisa.kernel.lambdaproof

import lisa.kernel.lambdafol.FOL._
import lisa.kernel.lambdaproof.RunningTheoryJudgement._
import lisa.kernel.lambdaproof.SequentCalculus._

import scala.collection.immutable.Set
import scala.collection.mutable.{Map => mMap}

/**
 * This class describes the theory, i.e. the context and language, in which theorems are proven.
 * A theory is built from scratch by introducing axioms and symbols first, then by definitional extensions.
 * The structure is one-way mutable: Once an axiom or definition has been introduced, it can't be removed.
 * On the other hand, theorems proven before the theory is extended will still hold.
 * A theorem only holds true within a specific theory.
 * A theory is responsible to make sure that a symbol already defined or present in the language can't
 * be redefined. If a theory needs to be extanded in two different ways, or if a theory and its extension need
 * to coexist independently, they should be different instances of this class.
 */
class RunningTheory {

  /**
   * A Justification is either a Theorem, an Axiom or a Definition
   */
  sealed abstract class Justification

  /**
   * A theorem encapsulate a sequent and assert that this sequent has been correctly proven and may be used safely in further proofs.
   */
  sealed case class Theorem private[RunningTheory] (name: String, proposition: Sequent, withSorry: Boolean) extends Justification

  /**
   * An axiom is any formula that is assumed and considered true within the theory. It can freely be used later in any proof.
   */
  sealed case class Axiom private[RunningTheory] (name: String, ax: Expression) extends Justification

  /**
   * A definition of a new symbol.
   */
  sealed case class Definition private[RunningTheory] (cst: Constant, expression: Expression, vars: Seq[Variable]) extends Justification

  private[lambdaproof] val theoryAxioms: mMap[String, Axiom] = mMap.empty
  private[lambdaproof] val theorems: mMap[String, Theorem] = mMap.empty

  private[lambdaproof] val definitions: mMap[Constant, Option[Definition]] = 
    mMap(equality -> None, top -> None, bot -> None, and -> None, or -> None, neg -> None, implies -> None, iff -> None, forall -> None, exists -> None, epsilon -> None)

  private[lambdaproof] val knownSymbols: mMap[Identifier, Constant] = 
    mMap(equality.id -> equality, top.id -> top, bot.id -> bot, and.id -> and, or.id -> or, neg.id -> neg, implies.id -> implies, iff.id -> iff, forall.id -> forall, exists.id -> exists, epsilon.id -> epsilon)

  /**
   * From a given proof, if it is true in the Running theory, add that theorem to the theory and returns it.
   * The proof's imports must be justified by the list of justification, and the conclusion of the theorem
   * can't contain symbols that do not belong to the theory.
   *
   * @param justifications The list of justifications of the proof's imports.
   * @param proof          The proof of the desired Theorem.
   * @return A Theorem if the proof is correct, None else
   */
  def makeTheorem(name: String, statement: Sequent, proof: SCProof, justifications: Seq[Justification]): RunningTheoryJudgement[this.Theorem] = {
    if (proof.conclusion == statement) proofToTheorem(name, proof, justifications)
    else InvalidJustification("The proof does not prove the claimed statement", None)
  }

  private def proofToTheorem(name: String, proof: SCProof, justifications: Seq[Justification]): RunningTheoryJudgement[this.Theorem] =
    if (proof.imports.forall(i => justifications.exists(j => isSameSequent(i, sequentFromJustification(j)))))
      if (belongsToTheory(proof.conclusion)) {
        val r = SCProofChecker.checkSCProof(proof)
        r match {
          case SCProofCheckerJudgement.SCValidProof(_, sorry) =>
            val usesSorry = sorry || justifications.exists(_ match {
              case Theorem(name, proposition, withSorry) => withSorry
              case Axiom(name, ax) => false
              case d: Definition => false
            })
            val thm = Theorem(name, proof.conclusion, usesSorry)
            theorems.update(name, thm)
            ValidJustification(thm)
          case r @ SCProofCheckerJudgement.SCInvalidProof(_, _, message) =>
            InvalidJustification("The given proof is incorrect: " + message, Some(r))
        }
      } else InvalidJustification("All symbols in the conclusion of the proof must belong to the theory. You need to add missing symbols to the theory.", None)
    else InvalidJustification("Not all imports of the proof are correctly justified.", None)


  def makeDefinition(cst: Constant, expression: Expression, vars: Seq[Variable]): RunningTheoryJudgement[this.Definition] = {
    if (cst.typ.depth == vars.length)
      if (flatTypeParameters(cst.typ) zip vars.map(_.typ) forall { case (a, b) => a == b })
        if (cst.typ == expression.typ)
          if (belongsToTheory(expression))
            if (isAvailable(cst))
              if (expression.freeVariables.isEmpty) {
                val newDef = Definition(cst, expression, vars)
                definitions.update(cst, Some(newDef))
                knownSymbols.update(cst.id , cst)
                RunningTheoryJudgement.ValidJustification(newDef)
              } else InvalidJustification("The definition is not allowed to contain schematic symbols or free variables.", None)
            else InvalidJustification("The specified symbol id is already part of the theory and can't be redefined.", None)
          else InvalidJustification("All symbols in the definition must belong to the theory. You need to add missing symbols to the theory.", None)
        else InvalidJustification("The type of the constant and the type of the expression must be the same.", None)
      else InvalidJustification("The types of the variables must match the type of the constant.", None)
    else InvalidJustification("The arity of the label must be equal to the number of parameters in the definition.", None)
  }

  /*

  /**
   * Introduce a new definition of a function in the theory. The symbol must not already exist in the theory
   * and the formula can't contain symbols that are not in the theory. The existence and uniqueness of an element
   * satisfying the definition's formula must first be proven. This is easy if the formula behaves as a shortcut,
   * for example f(x,y) = 3x+2y
   * but is much more general. The proof's conclusion must be of the form:  |- ∀args. ∃!out. phi
   *
   * @param proof          The proof of existence and uniqueness
   * @param justifications The justifications of the proof.
   * @param label          The desired label.
   * @param expression     The functional term defining the function symbol.
   * @param out            The variable representing the function's result in the formula
   * @param proven         A formula possibly stronger than `expression` that the proof proves. It is always correct if it is the same as "expression", but
   *                       if `expression` is less strong, this allows to make underspecified definitions.
   * @return A definition object if the parameters are correct,
   */
  def makeFunctionDefinition(
      proof: SCProof,
      justifications: Seq[Justification],
      label: ConstantFunctionLabel,
      out: VariableLabel,
      expression: LambdaTermFormula,
      proven: Formula
  ): RunningTheoryJudgement[this.FunctionDefinition] = {
    val LambdaTermFormula(vars, body) = expression
    if (vars.length == label.arity) {
      if (belongsToTheory(body)) {
        if (isAvailable(label)) {
          if (body.freeSchematicTermLabels.subsetOf((vars appended out).toSet) && body.schematicFormulaLabels.isEmpty) {
            if (proof.imports.forall(i => justifications.exists(j => isSameSequent(i, sequentFromJustification(j))))) {
              val r = SCProofChecker.checkSCProof(proof)
              r match {
                case SCProofCheckerJudgement.SCValidProof(_, sorry) =>
                  proof.conclusion match {
                    case Sequent(l, r) if l.isEmpty && r.size == 1 =>
                      if (isImplying(proven, body)) {
                        val subst = BinderFormula(ExistsOne, out, proven)
                        if (isSame(r.head, subst)) {
                          val usesSorry = sorry || justifications.exists(_ match {
                            case Theorem(name, proposition, withSorry) => withSorry
                            case Axiom(name, ax) => false
                            case d: Definition =>
                              d match {
                                case PredicateDefinition(label, expression) => false
                                case FunctionDefinition(label, out, expression, withSorry) => withSorry
                              }
                          })
                          val newDef = FunctionDefinition(label, out, expression, usesSorry)
                          funDefinitions.update(label, Some(newDef))
                          knownSymbols.update(label.id, label)
                          RunningTheoryJudgement.ValidJustification(newDef)
                        } else InvalidJustification("The proof is correct but its conclusion does not correspond to the claimed proven property.", None)
                      } else InvalidJustification("The proven property must be at least as strong as the desired definition, and it is not.", None)

                    case _ => InvalidJustification("The conclusion of the proof must have an empty left hand side, and a single formula on the right hand side.", None)
                  }
                case r @ SCProofCheckerJudgement.SCInvalidProof(_, path, message) => InvalidJustification("The given proof is incorrect: " + message, Some(r))
              }
            } else InvalidJustification("Not all imports of the proof are correctly justified.", None)
          } else InvalidJustification("The definition is not allowed to contain schematic symbols or free variables.", None)
        } else InvalidJustification("The specified symbol id is already part of the theory and can't be redefined.", None)
      } else InvalidJustification("All symbols in the conclusion of the proof must belong to the theory. You need to add missing symbols to the theory.", None)
    } else InvalidJustification("The arity of the label must be equal to the number of parameters in the definition.", None)
  }
*/


  def sequentFromJustification(j: Justification): Sequent = j match {
    case Theorem(name, proposition, _) => proposition
    case Axiom(name, ax) => Sequent(Set.empty, Set(ax))
    case Definition(cst, e, vars) =>
      if (cst.typ.isPredicate){
        val inner = Iff(vars.foldLeft(cst: Expression)(_(_)), vars.foldLeft(e)(_(_)))
        Sequent(Set(), Set(inner))
      } else {
        val inner = Equality(vars.foldLeft(cst: Expression)(_(_)), vars.foldLeft(e)(_(_)))
        Sequent(Set(), Set(inner))
      }
  }

  /**
   * Add a new axiom to the Theory. For example, if the theory contains the language and theorems
   * of Zermelo-Fraenkel Set Theory, this function may add the axiom of choice to it.
   * If the axiom belongs to the language of the theory, adds it and return true. Else, returns false.
   *
   * @param f the new axiom to be added.
   * @return true if the axiom was added to the theory, false else.
   */
  def addAxiom(name: String, f: Expression): Option[Axiom] = {
    if (f.typ == Formula && belongsToTheory(f)) {
      val ax = Axiom(name, f)
      theoryAxioms.update(name, ax)
      Some(ax)
    } else None
  }

  /**
   * Add a new symbol to the theory, without providing a definition. An ad-hoc definition can be
   * added via an axiom, typically if the desired object is not derivable in the base theory itself.
   * For example, This function can add the empty set symbol to a theory, and then an axiom asserting
   * that it is empty can be introduced as well.
   */

  def addSymbol(c: Constant): Unit = {
    if (isAvailable(c)) {
      knownSymbols.update(c.id, c)
      definitions.update(c, None)
    } else {}
  }

  /**
   * Add all constant symbols in the sequent. Note that this can't be reversed and will prevent from giving them a definition later.
   */
  def makeFormulaBelongToTheory(e: Expression): Unit = {
    e.constants.foreach(addSymbol)
  }

  /**
   * Add all constant symbols in the sequent. Note that this can't be reversed and will prevent from giving them a definition later.
   */
  def makeSequentBelongToTheory(s: Sequent): Unit = {
    s.left.foreach(makeFormulaBelongToTheory)
    s.right.foreach(makeFormulaBelongToTheory)
  }

  /**
   * Verify if a given expression belongs to the language of the theory.
   *
   * @param e The expression to check
   * @return Weather t belongs to the specified language.
   */
  def belongsToTheory(e: Expression): Boolean = e match {
    case v: Variable => true
    case c: Constant => isSymbol(c)
    case Application(f, arg) => belongsToTheory(f) && belongsToTheory(arg)
    case Lambda(v, t) => belongsToTheory(t)
  }

  /**
   * Verify if a given sequent belongs to the language of the theory.
   *
   * @param s The sequent to check
   * @return Weather s belongs to the specified language
   */
  def belongsToTheory(s: Sequent): Boolean =
    s.left.forall(belongsToTheory) && s.right.forall(belongsToTheory)

  /**
   * Public accessor to the set of symbol currently in the theory's language.
   *
   * @return the set of symbol currently in the theory's language.
   */
  def language(): List[(Constant, Option[Definition])] = definitions.toList

  /**
   * Check if a label is a symbol of the theory.
   */
  def isSymbol(cst: Constant): Boolean = definitions.contains(cst)

  /**
   * Check if a label is not already used in the theory.
   * @return
   */
  def isAvailable(label: Constant): Boolean = !knownSymbols.contains(label.id)

  /**
   * Public accessor to the current set of axioms of the theory
   *
   * @return the current set of axioms of the theory
   */
  def axiomsList(): Iterable[Axiom] = theoryAxioms.values

  /**
   * Verify if a given formula is an axiom of the theory
   */
  def isAxiom(f: Expression): Boolean = f.typ == Formula && theoryAxioms.exists(a => isSame(a._2.ax, f))

  /**
   * Get the Axiom that is the same as the given formula, if it exists in the theory.
   */
  def getAxiom(f: Expression): Option[Axiom] = if (f.typ == Formula) theoryAxioms.find(a => isSame(a._2.ax, f)).map(_._2) else None

  /**
   * Get the definition of the given label, if it is defined in the theory.
   */
  def getDefinition(label: Constant): Option[Definition] = definitions.get(label).flatten

  /**
   * Get the Axiom with the given name, if it exists in the theory.
   */
  def getAxiom(name: String): Option[Axiom] = theoryAxioms.get(name)

  /**
   * Get the Theorem with the given name, if it exists in the theory.
   */
  def getTheorem(name: String): Option[Theorem] = theorems.get(name)

  /**
   * Get the definition for the given identifier, if it is defined in the theory.
   */
  def getDefinition(name: Identifier): Option[Definition] = knownSymbols.get(name).flatMap(getDefinition)

}
object RunningTheory {

  /**
   * An empty theory suitable to reason about first order logic.
   */
  def PredicateLogic: RunningTheory = new RunningTheory()
}
