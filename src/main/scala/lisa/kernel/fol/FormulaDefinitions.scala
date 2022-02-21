package lisa.kernel.fol

/**
 * Definitions of formulas; analogous to [[TermDefinitions]].
 * Depends on [[FormulaLabelDefinitions]] and [[TermDefinitions]].
 */
private[fol] trait FormulaDefinitions extends FormulaLabelDefinitions with TermDefinitions {

  /**
   * The parent class of formulas.
   * A formula is a tree whose nodes are either terms or labeled by predicates or logical connectors.
   */
  sealed abstract class Formula extends TreeWithLabel[FormulaLabel] {
    def predicates: Set[ConstantPredicateLabel]
    def functions: Set[ConstantFunctionLabel]
    // def predicatesSchemas: Set[PredicateLabel] = predicates filter { case _: ConstantPredicateLabel => false; case _: SchematicPredicateLabel => true }
  }

  /**
   * The formula counterpart of [[PredicateLabel]].
   */
  final case class PredicateFormula(label: PredicateLabel, args: Seq[Term]) extends Formula {
    override def freeVariables: Set[VariableLabel] = args.foldLeft(Set.empty[VariableLabel])((prev, next) => prev union next.freeVariables)

    override def predicates: Set[ConstantPredicateLabel] = label match {
      case l: ConstantPredicateLabel => Set(l)
      case l: SchematicPredicateLabel => Set()
    }

    override def functions: Set[ConstantFunctionLabel] = args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.functions)
  }

  /**
   * The formula counterpart of [[ConnectorLabel]].
   */
  final case class ConnectorFormula(label: ConnectorLabel, args: Seq[Formula]) extends Formula {
    override def freeVariables: Set[VariableLabel] = args.foldLeft(Set.empty[VariableLabel])((prev, next) => prev union next.freeVariables)

    override def predicates: Set[ConstantPredicateLabel] = args.foldLeft(Set.empty[ConstantPredicateLabel])((prev, next) => prev union next.predicates)

    override def functions: Set[ConstantFunctionLabel] = args.foldLeft(Set.empty[ConstantFunctionLabel])((prev, next) => prev union next.functions)
  }

  /**
   * The formula counterpart of [[BinderLabel]].
   */
  final case class BinderFormula(label: BinderLabel, bound: VariableLabel, inner: Formula) extends Formula {
    override def freeVariables: Set[VariableLabel] = inner.freeVariables - bound

    override def predicates: Set[ConstantPredicateLabel] = inner.predicates

    override def functions: Set[ConstantFunctionLabel] = inner.functions
  }

  /**
   * Performs the substitution of x by r in f. May rename bound variables of f if necessary
   * to avoid capture of free variables in r.
   *
   * @param f The base formula
   * @param x A variable, which should be free in f
   * @param r A term that will replace x in f
   * @return f[r/x]
   */
  def substituteVariable(f: Formula, x: VariableLabel, r: Term): Formula = f match {
    case PredicateFormula(label, args) => PredicateFormula(label, args.map(substituteVariable(_, x, r)))
    case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(substituteVariable(_, x, r)))
    case BinderFormula(label, bound, inner) =>
      if (isSame(bound, x)) f
      else {
        val fv = r.freeVariables
        if (fv.contains(bound)) {
          val newBoundVariable = VariableLabel(freshId(fv.map(_.name), bound.name))
          val newInner = substituteVariable(inner, bound, VariableTerm(newBoundVariable))
          BinderFormula(label, newBoundVariable, substituteVariable(newInner, x, r))
        } else BinderFormula(label, bound, substituteVariable(inner, x, r))
      }
  }

  def bindAll(binder: BinderLabel, vars: Seq[VariableLabel], phi: Formula): Formula =
    vars.sortBy(_.name).foldLeft(phi)((f, v) => BinderFormula(binder, v, f))

  /**
   * Performs simultaneous substitution of multiple variables by multiple terms in a formula f.
   *
   * @param f The base formula
   * @param m A map from variables to terms.
   * @return t[m]
   */
  def simultaneousSubstitution(f: Formula, m: Map[VariableLabel, Term]): Formula = f match {
    case PredicateFormula(label, args) => PredicateFormula(label, args.map(simultaneousSubstitution(_, m)))
    case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(simultaneousSubstitution(_, m)))
    case BinderFormula(label, bound, inner) =>
      val newSubst = m - bound
      val fv = m.values.flatMap(_.freeVariables).toSet
      if (fv.contains(bound)) {
        val newBoundVariable = VariableLabel(freshId(fv.map(_.name), bound.name))
        val newInner = substituteVariable(inner, bound, VariableTerm(newBoundVariable))
        BinderFormula(label, newBoundVariable, simultaneousSubstitution(newInner, newSubst))
      } else BinderFormula(label, bound, simultaneousSubstitution(inner, newSubst))
  }

  /**
   * Instantiate a schematic predicate symbol in a formula, using higher-order instantiation.
   *
   * @param phi The base formula
   * @param p   The symbol to replace
   * @param psi A formula, seen as a function, that will replace p in t.
   * @param a   The "arguments" of psi when seen as a function rather than a ground formula.
   *            Those variables are replaced by the actual arguments of p.
   * @return phi[psi(a1,..., an)/p]
   */
  def instantiatePredicateSchema(phi: Formula, p: SchematicPredicateLabel, psi: Formula, a: Seq[VariableLabel]): Formula = {
    require(a.length == p.arity)
    phi match {
      case PredicateFormula(label, args) =>
        if (isSame(label, p)) simultaneousSubstitution(psi, (a zip args).toMap)
        else phi
      case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(instantiatePredicateSchema(_, p, psi, a)))
      case BinderFormula(label, bound, inner) =>
        val fv: Set[VariableLabel] = psi.freeVariables -- a
        if (fv.contains(bound)) {
          val newBoundVariable = VariableLabel(freshId(fv.map(_.name), bound.name))
          val newInner = substituteVariable(inner, bound, VariableTerm(newBoundVariable))
          BinderFormula(label, newBoundVariable, instantiatePredicateSchema(newInner, p, psi, a))
        } else BinderFormula(label, bound, instantiatePredicateSchema(inner, p, psi, a))
    }
  }

  /**
   * Instantiate a schematic function symbol in a formula, using higher-order instantiation.
   *
   * @param phi The base formula
   * @param f   The symbol to replace
   * @param r   A term, seen as a function, that will replace f in t.
   * @param a   The "arguments" of r when seen as a function rather than a ground term.
   *            Those variables are replaced by the actual arguments of f.
   * @return phi[r(a1,..., an)/f]
   */
  def instantiateFunctionSchema(phi: Formula, f: SchematicFunctionLabel, r: Term, a: Seq[VariableLabel]): Formula = {
    require(a.length == f.arity)
    phi match {
      case PredicateFormula(label, args) => PredicateFormula(label, args.map(instantiateFunctionSchema(_, f, r, a)))
      case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(instantiateFunctionSchema(_, f, r, a)))
      case BinderFormula(label, bound, inner) =>
        val fv: Set[VariableLabel] = r.freeVariables -- a.toSet
        if (fv.contains(bound)) {
          val newBoundVariable = VariableLabel(freshId(fv.map(_.name), bound.name))
          val newInner = substituteVariable(inner, bound, VariableTerm(newBoundVariable))
          BinderFormula(label, newBoundVariable, instantiateFunctionSchema(newInner, f, r, a))
        } else BinderFormula(label, bound, instantiateFunctionSchema(inner, f, r, a))
    }
  }

  def instantiateBinder(f: BinderFormula, t: Term): Formula = substituteVariable(f.inner, f.bound, t)

}
