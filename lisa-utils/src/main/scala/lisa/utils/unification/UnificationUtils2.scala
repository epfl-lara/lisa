package lisa.utils.unification

import lisa.kernel.fol.FOL.*
import lisa.utils.KernelHelpers.{_, given}
import lisa.utils.unification.FirstOrderUnifier.*

/**
 * General utilities for unification, substitution, and rewriting
 */
object UnificationUtils2 {

  /**
    * All the information required for performing rewrites.
    */
  case class RewriteContext(
    freeFormulaRules: Seq[(Formula, Formula)] = Seq.empty,
    freeTermRules: Seq[(Term, Term)] = Seq.empty,
    confinedFormulaRules: Seq[(Formula, Formula)] = Seq.empty,
    confinedTermRules: Seq[(Term, Term)] = Seq.empty,
    takenFormulaVars: Set[VariableFormulaLabel] = Set.empty,
    takenTermVars: Set[VariableLabel] = Set.empty
  ) {
    private var lastID: Identifier = freshId((takenFormulaVars ++ takenTermVars).map(_.id), "__rewriteVar__")
    
    def freshIdentifier = {
      lastID = freshId(Seq(lastID), "__rewriteVar__")
      lastID
    }

    def isFreeVariable(v: VariableLabel) = !takenTermVars.contains(v)
    def isFreeVariable(v: VariableFormulaLabel) = !takenFormulaVars.contains(v)
  }

  object RewriteContext {
    def empty = RewriteContext()
  }

  type TermSubstitution = Map[VariableLabel, Term]
  val TermSubstitution = Map // don't abuse pls O.o

  type FormulaSubstitution = Map[VariableFormulaLabel, Formula]
  val FormulaSubstitution = Map

  def matchTerm(reference: Term, template: Term, takenVariables: Iterator[VariableLabel] = Iterator.empty): Option[TermSubstitution] = {
    val context = RewriteContext(takenTermVars = takenVariables.toSet)
    matchTermRecursive(using context)(reference, template, TermSubstitution.empty)
  }

  def matchTermRecursive(using context: RewriteContext)(reference: Term, template: Term, substitution: TermSubstitution): Option[TermSubstitution] =
    if (reference == template)
      Some(substitution)
    else
      template.label match {
        case v @ VariableLabel(id) if context.isFreeVariable(v) => 
          // different label but substitutable or already correctly set
          if (reference.label != template.label && reference == substitution.getOrElse(v, reference)) Some(substitution + (v -> reference))
          // same and not already substituted to something else
          else if (reference.label == template.label && reference == substitution.getOrElse(v, reference)) Some(substitution)
          // unsat
          else None
        // {Constant, Schematic} FunctionLabel
        case _ =>
          if (reference.label != template.label) None
          else (reference.args zip template.args).foldLeft(Option(substitution)) { 
            case (Some(subs), (r, t)) => matchTermRecursive(r, t, subs)
            case (None, _) => None
          }
      }

  def matchFormula(reference: Formula, template: Formula, takenTermVariables: Iterator[VariableLabel] = Iterator.empty, takenFormulaVariables: Iterator[VariableFormulaLabel] = Iterator.empty): Option[(FormulaSubstitution, TermSubstitution)] = {
    val context = RewriteContext(
      takenTermVars = takenTermVariables.toSet,
      takenFormulaVars = takenFormulaVariables.toSet
    )
    matchFormulaRecursive(using context)(reference, template, FormulaSubstitution.empty, TermSubstitution.empty)
  }
  
  def matchFormulaRecursive(using context: RewriteContext)(reference: Formula, template: Formula, formulaSubstitution: FormulaSubstitution, termSubstitution: TermSubstitution): Option[(FormulaSubstitution, TermSubstitution)] =
    if (isSame(reference, template))
      Some((formulaSubstitution, termSubstitution))
    else
      (reference, template) match {
        case (BinderFormula(labelR, boundR, innerR), BinderFormula(labelT, boundT, innerT)) if labelR == labelT => {
          val freshVar = VariableLabel(context.freshIdentifier)

          // add a safety substitution to make sure bound variable isn't substituted, and check instantiated bodies
          val innerSubst = matchFormulaRecursive(
            substituteVariables(innerR, Map[VariableLabel, Term](boundR -> freshVar)),
            substituteVariables(innerT, Map[VariableLabel, Term](boundT -> freshVar)),
            formulaSubstitution,
            termSubstitution + (freshVar -> freshVar) // dummy substitution to make sure we don't attempt to match this as a variable
          )

          innerSubst match {
            case None => innerSubst
            case Some((sf, st)) => {
              val cleanSubst = (sf, st - freshVar) // remove the dummy substitution we added

              // were any formula substitutions involving the bound variable required?
              // if yes, not matchable
              if (cleanSubst._1.exists((k, v) => v.freeVariables.contains(freshVar))) None
              else Some(cleanSubst)
            }
          }
        }
        
        case (ConnectorFormula(labelR, argsR), ConnectorFormula(labelT, argsT)) if labelR == labelT => 
          if (argsR.length != argsT.length)
            // quick discard
            None
          else {
            // recursively check inner formulas
            val newSubstitution = (argsR zip argsT).foldLeft(Option(formulaSubstitution, termSubstitution)) {
              case (Some(substs), (ref, temp)) => matchFormulaRecursive(ref, temp, substs._1, substs._2)
              case (None, _) => None
            }
            newSubstitution
          }
        
        case (_, PredicateFormula(labelT: VariableFormulaLabel, _)) => 
          // can this variable be matched with the reference based on previously known or new substitutions?
          if (reference == formulaSubstitution.getOrElse(labelT, reference)) Some(formulaSubstitution + (labelT -> reference), termSubstitution)
          else if (template.label == reference.label && reference == formulaSubstitution.getOrElse(labelT, reference)) Some(formulaSubstitution, termSubstitution)
          else None
        
        case (PredicateFormula(labelR, argsR), PredicateFormula(labelT, argsT)) if labelR == labelT => 
          if (argsR.length != argsT.length)
            // quick discard
            None
          else {
            // our arguments are terms, match them recursively
            val newTermSubstitution = (argsR zip argsT).foldLeft(Option(termSubstitution)) {
              case (Some(tSubst), (ref, temp)) => matchTermRecursive(ref, temp, tSubst)
              case (None, _) => None
            }
            if (newTermSubstitution.isEmpty) None
            else Some(formulaSubstitution, newTermSubstitution.get)
          }
      }
}
