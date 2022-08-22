package lisa.kernel.fol

trait Substitutions extends FormulaDefinitions {

  /**
   * A lambda term to express a "term with holes". Main use is to be substituted in place of a function schema.
   * Morally equivalent to a 2-tuples containing the same informations.
   * @param vars The names of the "holes" in the term, necessarily of arity 0. The bound variables of the functional term.
   * @param body The term represented by the object, up to instantiation of the bound schematic variables in args.
   */
  case class LambdaTermTerm(vars: Seq[VariableLabel], body: Term) {
    def apply(args: Seq[Term]): Term = substituteVariables(body, (vars zip args).toMap)
  }

  /**
   * A lambda formula to express a "formula with holes". Main use is to be substituted in place of a predicate schema.
   * Morally equivalent to a 2-tuples containing the same informations.
   * @param vars The names of the "holes" in a formula, necessarily of arity 0. The bound variables of the functional formula.
   * @param body The formula represented by the object, up to instantiation of the bound schematic variables in args.
   */
  case class LambdaTermFormula(vars: Seq[VariableLabel], body: Formula) {
    def apply(args: Seq[Term]): Formula = {
      substituteVariables(body, (vars zip args).toMap)
    }
  }

  /**
   * A lambda formula to express a "formula with holes". Usefull for rules such as Iff substitution
   * Morally equivalent to a 2-tuples containing the same informations.
   * @param vars The names of the "holes" in a formula, necessarily of arity 0.
   * @param body The formula represented by the object, up to instantiation of the bound schematic variables in args.
   */
  case class LambdaFormulaFormula(vars: Seq[VariableFormulaLabel], body: Formula) {
    def apply(args: Seq[Formula]): Formula = {
      substituteFormulaVariables(body, (vars zip args).toMap)
      //instantiatePredicateSchemas(body, (vars zip (args map (LambdaTermFormula(Nil, _)))).toMap)
    }
  }

  //////////////////////////
  // **--- ON TERMS ---** //
  //////////////////////////

  /**
   * Performs simultaneous substitution of multiple variables by multiple terms in a term t.
   * @param t The base term
   * @param m A map from variables to terms.
   * @return t[m]
   */
  def substituteVariables(t: Term, m: Map[VariableLabel, Term]): Term = t match {
    case Term(label: VariableLabel, _) => m.getOrElse(label, t)
    case Term(label, args) => Term(label, args.map(substituteVariables(_, m)))
  }

  /**
   * Performs simultaneous substitution of schematic function symbol by "functional" terms, or terms with holes.
   * If the arity of one of the function symbol to substitute doesn't match the corresponding number of arguments, it will produce an error.
   * @param t The base term
   * @param m The map from schematic function symbols to "terms with holes". A such term is a pair containing a list of
   *          variable symbols (holes) and a term that is the body of the functional term.
   * @return t[m]
   */
  def instantiateTermSchemas(t: Term, m: Map[SchematicTermLabel, LambdaTermTerm]): Term = {
    require(m.forall { case (symbol, LambdaTermTerm(arguments, body)) => arguments.length == symbol.arity })
    t match {
      case Term(label: VariableLabel, _) => m.get(label).map(_.apply(Nil)).getOrElse(t)
      case Term(label, args) =>
        val newArgs = args.map(instantiateTermSchemas(_, m))
        label match {
          case label: ConstantFunctionLabel => Term(label, newArgs)
          case label: SchematicTermLabel =>
            m.get(label).map(_(newArgs)).getOrElse(Term(label, newArgs))
        }
    }
  }

  /////////////////////////////
  // **--- ON FORMULAS ---** //
  /////////////////////////////

  /**
   * Performs simultaneous substitution of multiple variables by multiple terms in a formula phi.
   *
   * @param f The base formula
   * @param m A map from variables to terms.
   * @return t[m]
   */
  def substituteVariables(phi: Formula, m: Map[VariableLabel, Term]): Formula = phi match {
    case PredicateFormula(label, args) => PredicateFormula(label, args.map(substituteVariables(_, m)))
    case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(substituteVariables(_, m)))
    case BinderFormula(label, bound, inner) =>
      val newSubst = m - bound
      val fv = m.values.flatMap(_.freeVariables).toSet
      if (fv.contains(bound)) {
        val newBoundVariable = VariableLabel(freshId(fv.map(_.name), bound.name))
        val newInner = substituteVariables(inner, Map(bound -> VariableTerm(newBoundVariable)))
        BinderFormula(label, newBoundVariable, substituteVariables(newInner, newSubst))
      } else BinderFormula(label, bound, substituteVariables(inner, newSubst))
  }

  def substituteFormulaVariables(phi: Formula, m: Map[VariableFormulaLabel, Formula]): Formula = phi match {
    case PredicateFormula(label: VariableFormulaLabel, _) => m.getOrElse(label, phi)
    case _: PredicateFormula => phi
    case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(substituteFormulaVariables(_, m)))
    case BinderFormula(label, bound, inner) =>
      val fv = m.values.flatMap(_.freeVariables).toSet
      if (fv.contains(bound)) {
        val newBoundVariable = VariableLabel(freshId(fv.map(_.name), bound.name))
        val newInner = substituteVariables(inner, Map(bound -> VariableTerm(newBoundVariable)))
        BinderFormula(label, newBoundVariable, substituteFormulaVariables(newInner, m))
      } else BinderFormula(label, bound, substituteFormulaVariables(inner, m))
  }

  /**
   * Performs simultaneous substitution of schematic function symbol by "functional" terms, or terms with holes.
   * If the arity of one of the function symbol to substitute doesn't match the corresponding number of arguments, it will produce an error.
   * @param phi The base formula
   * @param m The map from schematic function symbols to lambda expressions Term(s) -> Term.
   * @return phi[m]
   */
  def instantiateTermSchemas(phi: Formula, m: Map[SchematicTermLabel, LambdaTermTerm]): Formula = {
    require(m.forall { case (symbol, LambdaTermTerm(arguments, body)) => arguments.length == symbol.arity })
    phi match {
      case PredicateFormula(label, args) => PredicateFormula(label, args.map(a => instantiateTermSchemas(a, m)))
      case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(instantiateTermSchemas(_, m)))
      case BinderFormula(label, bound, inner) =>
        val newSubst = m - bound
        val fv: Set[VariableLabel] = newSubst.flatMap { case (symbol, LambdaTermTerm(arguments, body)) => body.freeVariables }.toSet
        if (fv.contains(bound)) {
          val newBoundVariable = VariableLabel(freshId(fv.map(_.name), bound.name))
          val newInner = substituteVariables(inner, Map(bound -> VariableTerm(newBoundVariable)))
          BinderFormula(label, newBoundVariable, instantiateTermSchemas(newInner, newSubst))
        } else BinderFormula(label, bound, instantiateTermSchemas(inner, newSubst))
    }
  }

  /**
   * Instantiate a schematic predicate symbol in a formula, using higher-order instantiation.
   *
   * @param phi The base formula
   * @param m The map from schematic predicate symbols to lambda expressions Term(s) -> Formula.
   * @return phi[m]
   */
  def instantiatePredicateSchemas(phi: Formula, m: Map[SchematicVarOrPredLabel, LambdaTermFormula]): Formula = {
    require(m.forall { case (symbol, LambdaTermFormula(arguments, body)) => arguments.length == symbol.arity })
    phi match {
      case PredicateFormula(label, args) =>
        label match {
          case label: SchematicPredicateLabel if m.contains(label) => m(label)(args)
          case _ => phi
        }
      case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(instantiatePredicateSchemas(_, m)))
      case BinderFormula(label, bound, inner) =>
        val fv: Set[VariableLabel] = (m.flatMap { case (symbol, LambdaTermFormula(arguments, body)) => body.freeVariables }).toSet
        if (fv.contains(bound)) {
          val newBoundVariable = VariableLabel(freshId(fv.map(_.name), bound.name))
          val newInner = substituteVariables(inner, Map(bound -> VariableTerm(newBoundVariable)))
          BinderFormula(label, newBoundVariable, instantiatePredicateSchemas(newInner, m))
        } else BinderFormula(label, bound, instantiatePredicateSchemas(inner, m))
    }
  }

  /**
   * Instantiate a schematic connector symbol in a formula, using higher-order instantiation.
   *
   * @param phi The base formula
   * @param m The map from schematic function symbols to lambda expressions Formula(s) -> Formula.
   * @return phi[m]
   */
  def instantiateConnectorSchemas(phi: Formula, m: Map[SchematicConnectorLabel, LambdaFormulaFormula]): Formula = {
    require(m.forall { case (symbol, LambdaFormulaFormula(arguments, body)) => arguments.length == symbol.arity })
    phi match {
      case _: PredicateFormula => phi
      case ConnectorFormula(label, args) =>
        label match {
          case label: SchematicConnectorLabel  if m.contains(label) => m(label)(args)
          case _ => ConnectorFormula(label, args.map(instantiateConnectorSchemas(_, m)))
        }
      case BinderFormula(label, bound, inner) =>
        val fv: Set[VariableLabel] = (m.flatMap { case (symbol, LambdaFormulaFormula(arguments, body)) => body.freeVariables }).toSet
        if (fv.contains(bound)) {
          val newBoundVariable = VariableLabel(freshId(fv.map(_.name), bound.name))
          val newInner = substituteVariables(inner, Map(bound -> VariableTerm(newBoundVariable)))
          BinderFormula(label, newBoundVariable, instantiateConnectorSchemas(newInner, m))
        } else BinderFormula(label, bound, instantiateConnectorSchemas(inner, m))
    }
  }

  def instantiateBinder(f: BinderFormula, t: Term): Formula = substituteVariables(f.inner, Map(f.bound -> t))

}
