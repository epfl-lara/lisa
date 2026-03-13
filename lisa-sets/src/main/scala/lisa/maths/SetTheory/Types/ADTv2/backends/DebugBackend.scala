package lisa.maths.SetTheory.Types.ADTv2.backends

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.ADTSpec

/**
 * Debug backend used to test ADTv2 interpreter output shape before
 * integrating with a real LISA backend.
 */
final class DebugBackend extends Backend {
  type SymbolHandle = String
  type FormulaHandle = String
  type TheoremHandle = String
  type TermHandle = String

  private var nextId: Int = 0
  private def fresh(prefix: String): String = {
    nextId += 1
    s"${prefix}_$nextId"
  }

  override def symbol(name: String): SymbolHandle = s"sym:$name"

  override def define(name: String, body: TermHandle): SymbolHandle = s"def:$name=$body"

  override def defineADT(spec: ADTSpec): ADTResult = {
    val typeSym = symbol(spec.name)
    val ctors = spec.constructors.map(c => c.name -> symbol(s"${spec.name}.${c.name}")).toMap
    val ctorTypes = spec.constructors.map(c => c.name -> s"typing:${spec.name}.${c.name}").toMap
    val discriminators = spec.constructors.map(c => c.name -> symbol(s"is_${c.name}")).toMap
    val selectors = spec.constructors.map(c => c.name -> c.args.indices.map(i => symbol(s"${c.name}.sel$i")).toSeq).toMap
    val induction = fresh(s"thm:${spec.name}.induction")
    ADTResult(typeSym, ctors, ctorTypes, discriminators, selectors, induction)
  }

  override def variable(name: String): TermHandle = s"var:$name"

  override def apply(symbol: SymbolHandle, args: Seq[TermHandle]): TermHandle =
    s"app($symbol,${args.mkString(",")})"

  override def equality(lhs: TermHandle, rhs: TermHandle): FormulaHandle = s"eq($lhs,$rhs)"

  override def implies(premise: FormulaHandle, conclusion: FormulaHandle): FormulaHandle = s"impl($premise,$conclusion)"

  override def conjunction(conjuncts: Seq[FormulaHandle]): FormulaHandle = s"and(${conjuncts.mkString(",")})"

  override def forall(variableName: String, domain: TermHandle, body: FormulaHandle): FormulaHandle =
    s"forall($variableName:$domain,$body)"

  override def exists(variableName: String, domain: TermHandle, body: FormulaHandle): FormulaHandle =
    s"exists($variableName:$domain,$body)"

  override def hasType(term: TermHandle, tpe: TermHandle): FormulaHandle = s"hasType($term,$tpe)"

  override def theorem(name: String, statement: FormulaHandle): TheoremHandle = s"thm:$name::$statement"

  override def theoremLabel(thm: TheoremHandle): String = thm
}
