package lisa.maths.SetTheory.Types.ADTv2.backends

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.ADTSpec
import lisa.maths.SetTheory.SetTheory.*
import lisa.maths.SetTheory.Types.TypingHelpers.::
import lisa.utils.fol.FOL.Variable as FolVariable
import lisa.utils.K.{given_Conversion_String_Identifier}

import lisa.SetTheoryLibrary
import lisa.utils.prooflib.OutputManager

/**
 * Debug backend used to test ADTv2 interpreter output shape before
 * integrating with a real LISA backend.
 */
final class NewBackend(
  using val lib: SetTheoryLibrary.type,
        val om: OutputManager
) extends Backend {
  
  import lib.{given, *} // imports theorem/definition syntax in this context

  type SymbolHandle = Expr[Ind]
  type FormulaHandle = Expr[Prop]
  type TheoremHandle = THM
  type TermHandle = Expr[Ind]

  private var nextId: Int = 0

  private def fresh(prefix: String): String = {
    nextId += 1
    s"${prefix}_$nextId"
  }


  // Symbol and definition creation

  override def symbol(name: String): SymbolHandle = {
     Constant[Ind](name)
  }

  override def define(name: String, body: TermHandle): SymbolHandle = {
      // Store as a real global definition (same infrastructure used by Untyped definitions).
      // DirectDefinition writes into library/theory definition tables.
      require(body.freeVars.isEmpty, s"Definition '$name' must be closed; free vars: ${body.freeVars.mkString(", ")}")
      lib.DirectDefinition[Ind](name, sourcecode.Line(0), sourcecode.File("ADTv2/NewBackend.scala"))(body, Seq.empty).cst
  }

  override def defineADT(spec: ADTSpec): ADTResult = {
    val typeSym = symbol(spec.name)
    val ctors = spec.constructors.map(c => c.name -> symbol(???)).toMap
    val ctorTypes = spec.constructors.map(c => c.name -> ???).toMap
    val discriminators = spec.constructors.map(c => c.name -> symbol(???)).toMap
    val selectors = spec.constructors.map(c => c.name -> c.args.indices.map(i => symbol(???)).toSeq).toMap
    val induction = theorem(fresh(s"thm:${spec.name}.induction"), ???)
    ADTResult(typeSym, ctors, ctorTypes, discriminators, selectors, induction)
  }


  // Term construction

  override def variable(name: String): TermHandle = FolVariable[Ind](name)

  override def apply(symbol: SymbolHandle, args: Seq[TermHandle]): TermHandle =
    // Use unsafe application since we don't know the function type at compile time
    // Multiapp.unsafe(symbol, args).asInstanceOf[TermHandle]
    
    // Return an error term for now
    Constant[Ind](s"apply(${symbol}, ${args.mkString(", ")})")


  // Formula construction

  override def equality(lhs: TermHandle, rhs: TermHandle): FormulaHandle =
    (lhs === rhs)

  override def implies(premise: FormulaHandle, conclusion: FormulaHandle): FormulaHandle =
    (premise ==> conclusion)

  override def conjunction(conjuncts: Seq[FormulaHandle]): FormulaHandle =
    if conjuncts.isEmpty then True
    else conjuncts.reduce(_ /\ _)

  override def forall(variableName: String, domain: TermHandle, body: FormulaHandle): FormulaHandle = {
    val x = FolVariable[Ind](variableName)
    ∀(x ∈ domain, body)
  }

  override def exists(variableName: String, domain: TermHandle, body: FormulaHandle): FormulaHandle = {
    val x = FolVariable[Ind](variableName)
    ∃(x ∈ domain, body)
  }


  // Typing and theorem registration

  override def hasType(term: TermHandle, tpe: TermHandle): FormulaHandle =
    (term :: tpe)

  override def theorem(name: String, statement: FormulaHandle): TheoremHandle =
    throw new NotImplementedError(
      "Creating theorems requires a proof context. " +
      "Use this backend with pre-existing theorems or extend it to support theorem creation."
    )

  override def theoremLabel(thm: TheoremHandle): String = thm.fullName
}
