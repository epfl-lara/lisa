package lisa.kernel.fol

/**
 * Definitions of terms; depends on [[TermLabelDefinitions]].
 */
private[fol] trait TermDefinitions extends TermLabelDefinitions {

  protected trait TreeWithLabel[A] {
    val label: A

    def freeVariables: Set[VariableLabel]

    def functions: Set[ConstantFunctionLabel]
  }


  /**
   * The parent classes of terms.
   * A term is a tree with nodes labeled by functions labels or variables.
   * The number of children of a node is restricted by the arity imposed by the label.
   */
  sealed abstract class Term extends TreeWithLabel[TermLabel]


  /**
   * A term which consists of a single variable.
   *
   * @param label The label of the variable.
   */
  final case class VariableTerm(label: VariableLabel) extends Term {
    override def freeVariables: Set[VariableLabel] = Set(label)

    override def functions: Set[ConstantFunctionLabel] = Set.empty
  }

  /**
   * A term labelled by a function symbol. It must contain a number of children equal to the arity of the symbol
   *
   * @param label The label of the node
   * @param args  children of the node. The number of argument must be equal to the arity of the function.
   */
  final case class FunctionTerm(label: FunctionLabel, args: Seq[Term]) extends Term {
    require(label.arity == args.size)

    override def freeVariables: Set[VariableLabel] = args.foldLeft(Set.empty[VariableLabel])((prev, next) => prev union next.freeVariables)

    override def functions: Set[ConstantFunctionLabel] = label match {
      case l:ConstantFunctionLabel => args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.functions) + l
      case l:SchematicFunctionLabel => args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.functions)
    }

    val arity: Int = args.size
  }

  /**
   * Performs the substitution of x by r in t.
   *
   * @param t The base term
   * @param x A variable, which should be free in t
   * @param r A term that will replace x in t.
   * @return t[r/x]
   */
  def substituteVariable(t: Term, x: VariableLabel, r: Term): Term = t match {
    case VariableTerm(label) => if (isSame(label, x)) r else t
    case FunctionTerm(label, args) => FunctionTerm(label, args.map(substituteVariable(_, x, r)))
  }

  /**
   * Performs simultaneous substitution of multiple variables by multiple terms in a term t.
   *
   * @param t The base term
   * @param m A map from variables to terms.
   * @return t[m]
   */
  def simultaneousSubstitution(t: Term, m: Map[VariableLabel, Term]): Term = t match {
    case VariableTerm(label) => m.getOrElse(label, t)
    case FunctionTerm(label, args) => FunctionTerm(label, args.map(simultaneousSubstitution(_, m)))
  }

  /**
   * instantiate a schematic function symbol in a term, using higher-order instantiation.
   *
   * @param t The base term
   * @param f The symbol to replace
   * @param r A term, seen as a function, that will replace f in t.
   * @param a The "arguments" of r when seen as a function rather than a ground term.
   *          Those variables are replaced by the actual arguments of f.
   * @return t[r(a1,..., an)/f]
   */
  def instantiateFunctionSchema(t: Term, f: SchematicFunctionLabel, r: Term, a: List[VariableLabel]): Term = {
    require(a.length == f.arity)
    t match {
      case VariableTerm(label) => t
      case FunctionTerm(label, args) =>
        val newArgs = args.map(instantiateFunctionSchema(_, f, r, a))
        if (isSame(label, f)) simultaneousSubstitution(r, (a zip newArgs).toMap)
        else FunctionTerm(label, newArgs)
    }
  }
}
