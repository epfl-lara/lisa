package lisa.kernel.proof

import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.proof.SCProofChecker.*
import lisa.kernel.fol.FOL.*

import scala.collection.mutable.Map as mMap
import scala.collection.mutable.Set as mSet
import scala.collection.immutable.Set

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
    final case class Theorem private[RunningTheory](proposition: Sequent) extends Justification
    /**
     * An axiom is any formula that is assumed and considered true within the theory. It can freely be used later in any proof.
     */
    final case class Axiom private[RunningTheory](ax: Formula) extends Justification

    /**
     * A definition can be either a PredicateDefinition or a FunctionDefinition.
     */
    sealed abstract class Definition extends Justification

    /**
     * Define a predicate symbol as a shortcut for a formula. Example : P(x,y) :=   ∃!z. (x=y+z)
     * @param label The name and arity of the new symbol
     * @param args The variables representing the arguments of the predicate in the formula phi.
     * @param phi The formula defining the predicate.
     */
    final case class PredicateDefinition private[RunningTheory](label: ConstantPredicateLabel, args: Seq[VariableLabel], phi:Formula) extends Definition

    /**
     * Define a function symbol as the unique element that has some property. The existence and uniqueness
     * of that elements must have been proven before obtaining such a definition. Example
     * f(x,y) := the "z" s.t. x=y+z
     * @param label The name and arity of the new symbol
     * @param args The variables representing the arguments of the predicate in the formula phi.
     * @param out The variable representing the result of the function in phi
     * @param phi The formula defining the function.
     */
    final case class FunctionDefinition private[RunningTheory](label: ConstantFunctionLabel, args: Seq[VariableLabel], out: VariableLabel, phi: Formula) extends Definition


    private[proof] val theoryAxioms : mSet[Axiom] = mSet.empty
    private[proof] val funDefinitions: mMap[FunctionLabel, Option[FunctionDefinition]] = mMap.empty
    private[proof] val predDefinitions: mMap[PredicateLabel, Option[PredicateDefinition]] = mMap(equality -> None)

    /**
     * Check if a label is a symbol of the theory
     */
    def isAcceptedFunctionLabel(label:FunctionLabel): Boolean = funDefinitions.contains(label)
    /**
     * Check if a label is a symbol of the theory
     */
    def isAcceptedPredicateLabel(label:PredicateLabel): Boolean = predDefinitions.contains(label)

    /**
     * From a given proof, if it is true in the Running theory, returns a theorem that is valid in the given theory.
     * The proof's imports must be justified by the list of justification, and the conclusion of the theorem
     * can't contain symbols that do not belong to the theory.
     * @param justifications The list of justifications of the proof's imports.
     * @param p The proof of the desired Theorem.
     * @return A Theorem if the proof is correct, None else
     */
    def proofToTheorem(p: SCProof, justifications:Seq[Justification]): Option[this.Theorem] =
        if (checkProofWithinTheory(p, justifications) && belongsToTheory(p.conclusion))
            Some(Theorem(p.conclusion))
        else None


    /**
     * Introduce a new definition of a predicate in the theory. The symbol must not already exist in the theory
     * and the formula can't contain symbols that are not in the theory.
     * @param label The desired label.
     * @param args The variables representing the arguments of the predicate in the formula phi.
     * @param phi The formula defining the predicate.
     * @return A definition object if the parameters are correct,
     */
    def makePredicateDefinition(label: ConstantPredicateLabel, args: Seq[VariableLabel], phi: Formula): Option[this.PredicateDefinition] = {
        if (belongsToTheory(phi) && !isAcceptedPredicateLabel(label)) {
            val newDef = PredicateDefinition(label, args, phi)
            predDefinitions.update(label, Some(newDef))
            Some(newDef)
        } else {
            None
        }
    }

    /**
     * Introduce a new definition of a function in the theory. The symbol must not already exist in the theory
     * and the formula can't contain symbols that are not in the theory. The existence and uniqueness of an element
     * satisfying the definition's formula must first be proven. This is easy if the formula behaves as a shortcut,
     * for example f(x,y) = 3x+2y
     * but is much more general. The proof's conclusion must be of the form:  |- ∀args. ∃!out. phi
     * @param proof The proof of existence and uniqueness
     * @param justifications The justifications of the proof.
     * @param label The desired label.
     * @param args The variables representing the arguments of the predicate in the formula phi.
     * @param out The variable representing the function's result in the formula
     * @param phi The formula defining the predicate.
     * @return A definition object if the parameters are correct,
     */
    def makeFunctionDefinition(proof: SCProof, justifications:Seq[Justification], label: ConstantFunctionLabel, args: Seq[VariableLabel], out: VariableLabel, phi: Formula): Option[this.FunctionDefinition] = {
        if (belongsToTheory(phi) && !isAcceptedFunctionLabel(label) && checkProofWithinTheory(proof, justifications)) {
        
            proof.conclusion match{
                case Sequent(l, r)  if l.isEmpty && r.size == 1 =>
                    val subst = bindAll(ExistsOne, args, phi)
                    if (isSame(r.head, subst)){
                        val newDef = FunctionDefinition(label, args, out, phi)
                        funDefinitions.update(label, Some(newDef))
                        Some(newDef)
                    }
                    else None
                  
                case _ => None
            }
        } else {
            None
        }
    }



    /**
     * Verify is a proof is correct withing a given Theory. It separately verifies if the proof is correct from
     * a pure sequent calculus point of view, and if definitions and theorem imported into the proof are indeed
     * part of the theory.
     * 
     */
    def checkProofWithinTheory(proof: SCProof, justifications: Seq[Justification]): Boolean = {
    
        if (belongsToTheory(proof.conclusion)){
            if (proof.imports.forall(i => justifications.exists( j => isSameSequent(i, sequentFromJustification(j))) ))
                true
            else
                false
        }
        else false
    }

    private def sequentFromJustification(j:Justification): Sequent = j match {
        case Theorem(proposition) => proposition
        case Axiom(ax) => Sequent(Set.empty, Set(ax))
        case PredicateDefinition(label, args, phi) =>
            val inner = ConnectorFormula(Iff, Seq(PredicateFormula(label, args.map(VariableTerm.apply)), phi))
            Sequent(Set(), Set(bindAll(Forall, args, inner)))
        case FunctionDefinition(label, args, out, phi) =>
            val inner = BinderFormula(Forall, out,
                ConnectorFormula(Iff, Seq(
                    PredicateFormula(equality, Seq(FunctionTerm(label, args.map(VariableTerm.apply)), VariableTerm(out))),
                    phi
                ))
            )
            Sequent(Set(), Set(
                bindAll(Forall, args, inner)
            ))

    }




    /**
     * Verify if a given formula belongs to some language
     * @param phi The formula to check
     * @return Weather phi belongs to the specified language
     */
    def belongsToTheory(phi:Formula):Boolean = phi match {
        case PredicateFormula(label, args) =>
            label match {
                case _: ConstantPredicateLabel => isAcceptedPredicateLabel(label) && args.forall(belongsToTheory)
                case _: SchematicPredicateLabel => args.forall(belongsToTheory)
            }
        case ConnectorFormula(label, args) => args.forall(belongsToTheory)
        case BinderFormula(label, bound, inner) => belongsToTheory(inner)
    }

    def makeFormulaBelongToTheory(phi:Formula) : Unit = {
        phi.predicates.foreach(addSymbol)
        phi.functions.foreach(addSymbol)
    }
    /**
     * Verify if a given term belongs to some language
     * @param t The term to check
     * @return Weather t belongs to the specified language
     */
    def belongsToTheory(t:Term):Boolean = t match {
        case VariableTerm(label) => true
        case FunctionTerm(label, args) => label match {
            case _: ConstantFunctionLabel => isAcceptedFunctionLabel(label) && args.forall(belongsToTheory(_))
            case _: SchematicFunctionLabel => args.forall(belongsToTheory(_))
        }

    }
    /**
     * Verify if a given sequent belongs to some language
     * @param s The sequent to check
     * @return Weather s belongs to the specified language
     */
    def belongsToTheory(s:Sequent):Boolean =
        s.left.forall(belongsToTheory(_)) && s.right.forall(belongsToTheory(_))


    def makeSequentBelongToTheory(s:Sequent): Unit = {
        s.left.foreach(makeFormulaBelongToTheory)
        s.right.foreach(makeFormulaBelongToTheory)
    }
    

    /**
     * Add a new axiom to the Theory. For example, if the theory contains the language and theorems
     * of Zermelo-Fraenkel Set Theory, this function can add the axiom of choice to it.
     * If the axiom belongs to the language of the theory, adds it and return true. Else, returns false.
     * @param f the new axiom to be added.
     * @return true if the axiom was added to the theory, false else.
     */
    def addAxiom(f:Formula):Boolean = {
        if (belongsToTheory(f)){
            theoryAxioms.add(Axiom(f))
            true
        }
        else false
    }

    /**
     * Add a new symbol to the theory, without providing a definition. An ad-hoc definition can be
     * added via an axiom, typically if the desired object is not derivable in the base theory itself.
     * For example, This function can add the empty set symbol to a theory, and then an axiom asserting
     * the it is empty can be introduced as well.
     */
    def addSymbol(l:FunctionLabel):Unit = funDefinitions.update(l, None)
    def addSymbol(l:PredicateLabel):Unit = predDefinitions.update(l, None)

    /**
     * Public accessor to the set of symbol currently in the theory's language.
     * @return the set of symbol currently in the theory's language.
     */
    def language: (List[(FunctionLabel, Option[FunctionDefinition])], List[(PredicateLabel, Option[PredicateDefinition])]) = (funDefinitions.toList, predDefinitions.toList)
    /**
     * Public accessor to the current set of axioms of the theory
     * @return the current set of axioms of the theory
     */
    def getAxioms: List[Axiom] = theoryAxioms.toList

    /**
     * Verify if a given formula is an axiom of the theory
     * @param f the candidate axiom
     * @return wether f is an axiom of the theory
     */
    def isAxiom(f:Formula): Boolean = theoryAxioms.exists(a => isSame(a.ax,f))

}
object RunningTheory {
    /**
     * An empty theory suitable to reason about first order logic.
     */
    def PredicateLogic: RunningTheory = RunningTheory()
}

