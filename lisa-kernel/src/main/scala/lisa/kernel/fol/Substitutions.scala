package lisa.kernel.fol

trait Substitutions extends FormulaDefinitions {

  /**
   * A lambda term to express a "term with holes". Main use is to be substituted in place of a function schema or variable.
   * Also used for some deduction rules.
   * Morally equivalent to a 2-tuples containing the same informations.
   * @param vars The names of the "holes" in the term, necessarily of arity 0. The bound variables of the functional term.
   * @param body The term represented by the object, up to instantiation of the bound schematic variables in args.
   */
  case class LambdaTermTerm(vars: Seq[VariableLabel], body: Term) {
    def apply(args: Seq[Term]): Term = substituteVariablesInTerm(body, (vars zip args).toMap)
  }

  /**
   * A lambda formula to express a "formula with term holes". Main use is to be substituted in place of a predicate schema.
   * Also used for some deduction rules.
   * Morally equivalent to a 2-tuples containing the same informations.
   * @param vars The names of the "holes" in a formula, necessarily of arity 0. The bound variables of the functional formula.
   * @param body The formula represented by the object, up to instantiation of the bound schematic variables in args.
   */
  case class LambdaTermFormula(vars: Seq[VariableLabel], body: Formula) {
    def apply(args: Seq[Term]): Formula = {
      substituteVariablesInFormula(body, (vars zip args).toMap)
    }
  }

  /**
   * A lambda formula to express a "formula with formula holes". Main use is to be substituted in place of a connector schema.
   * Also used for some deduction rules.
   * Morally equivalent to a 2-tuples containing the same informations.
   * @param vars The names of the "holes" in a formula, necessarily of arity 0.
   * @param body The formula represented by the object, up to instantiation of the bound schematic variables in args.
   */
  case class LambdaFormulaFormula(vars: Seq[VariableFormulaLabel], body: Formula) {
    def apply(args: Seq[Formula]): Formula = {
      substituteFormulaVariables(body, (vars zip args).toMap)
      // instantiatePredicateSchemas(body, (vars zip (args map (LambdaTermFormula(Nil, _)))).toMap)
    }
  }

  //////////////////////////
  // **--- ON TERMS ---** //
  //////////////////////////

  /**
   * Performs simultaneous substitution of multiple variables by multiple terms in a term.
   * @param t The base term
   * @param m A map from variables to terms.
   * @return t[m]
   */
  def substituteVariablesInTerm(t: Term, m: Map[VariableLabel, Term]): Term = t match {
    case Term(label: VariableLabel, _) => m.getOrElse(label, t)
    case Term(label, args) => Term(label, args.map(substituteVariablesInTerm(_, m)))
  }

  /**
   * Performs simultaneous substitution of schematic function symbol by "functional" terms, or terms with holes.
   * If the arity of one of the function symbol to substitute doesn't match the corresponding number of arguments, it will produce an error.
   * @param t The base term
   * @param m The map from schematic function symbols to lambda expressions Term(s) -> Term [[LambdaTermTerm]].
   * @return t[m]
   */
  def instantiateTermSchemasInTerm(t: Term, m: Map[SchematicTermLabel, LambdaTermTerm]): Term = {
    require(m.forall { case (symbol, LambdaTermTerm(arguments, body)) => arguments.length == symbol.arity })
    t match {
      case Term(label: VariableLabel, _) => m.get(label).map(_.apply(Nil)).getOrElse(t)
      case Term(label, args) =>
        val newArgs = args.map(instantiateTermSchemasInTerm(_, m))
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
   * Performs simultaneous substitution of multiple variables by multiple terms in a formula.
   *
   * @param phi The base formula
   * @param m A map from variables to terms
   * @return t[m]
   */
  def substituteVariablesInFormula(phi: Formula, m: Map[VariableLabel, Term], takenIds: Seq[Identifier] = Seq[Identifier]()): Formula = phi match {
    case PredicateFormula(label, args) => PredicateFormula(label, args.map(substituteVariablesInTerm(_, m)))
    case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(substituteVariablesInFormula(_, m)))
    case BinderFormula(label, bound, inner) =>
      val newSubst = m - bound
      val newTaken = takenIds :+ bound.id
      val fv = m.values.flatMap(_.freeVariables).toSet
      if (fv.contains(bound)) {
        val newBoundVariable = VariableLabel(freshId(fv.map(_.name) ++ m.keys.map(_.id) ++ newTaken, bound.name))
        val newInner = substituteVariablesInFormula(inner, Map(bound -> VariableTerm(newBoundVariable)), newTaken)
        BinderFormula(label, newBoundVariable, substituteVariablesInFormula(newInner, newSubst, newTaken))
      } else BinderFormula(label, bound, substituteVariablesInFormula(inner, newSubst, newTaken))
  }

  /**
   * Performs simultaneous substitution of multiple formula variables by multiple formula terms in a formula.
   *
   * @param phi The base formula
   * @param m A map from variables to terms
   * @return t[m]
   */
  def substituteFormulaVariables(phi: Formula, m: Map[VariableFormulaLabel, Formula], takenIds: Seq[Identifier] = Seq[Identifier]()): Formula = phi match {
    case PredicateFormula(label: VariableFormulaLabel, _) => m.getOrElse(label, phi)
    case _: PredicateFormula => phi
    case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(substituteFormulaVariables(_, m, takenIds)))
    case BinderFormula(label, bound, inner) =>
      val fv = m.values.flatMap(_.freeVariables).toSet
      val newTaken = takenIds :+ bound.id
      if (fv.contains(bound)) {
        val newBoundVariable = VariableLabel(freshId(fv.map(_.name) ++ newTaken, bound.name))
        val newInner = substituteVariablesInFormula(inner, Map(bound -> VariableTerm(newBoundVariable)), newTaken)
        BinderFormula(label, newBoundVariable, substituteFormulaVariables(newInner, m, newTaken))
      } else BinderFormula(label, bound, substituteFormulaVariables(inner, m, newTaken))
  }

  /**
   * Performs simultaneous substitution of schematic function symbol by "functional" terms, or terms with holes.
   * If the arity of one of the predicate symbol to substitute doesn't match the corresponding number of arguments, it will produce an error.
   * @param phi The base formula
   * @param m The map from schematic function symbols to lambda expressions Term(s) -> Term [[LambdaTermTerm]].
   * @return phi[m]
   */
  def instantiateTermSchemas(phi: Formula, m: Map[SchematicTermLabel, LambdaTermTerm]): Formula = {
    require(m.forall { case (symbol, LambdaTermTerm(arguments, body)) => arguments.length == symbol.arity })
    phi match {
      case PredicateFormula(label, args) => PredicateFormula(label, args.map(a => instantiateTermSchemasInTerm(a, m)))
      case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(instantiateTermSchemas(_, m)))
      case BinderFormula(label, bound, inner) =>
        val newSubst = m - bound
        val fv: Set[VariableLabel] = newSubst.flatMap { case (symbol, LambdaTermTerm(arguments, body)) => body.freeVariables }.toSet
        if (fv.contains(bound)) {
          val newBoundVariable = VariableLabel(freshId(fv.map(_.name) ++ m.keys.map(_.id), bound.name))
          val newInner = substituteVariablesInFormula(inner, Map(bound -> VariableTerm(newBoundVariable)))
          BinderFormula(label, newBoundVariable, instantiateTermSchemas(newInner, newSubst))
        } else BinderFormula(label, bound, instantiateTermSchemas(inner, newSubst))
    }
  }

  /**
   * Instantiate a schematic predicate symbol in a formula, using higher-order instantiation.
   * If the arity of one of the connector symbol to substitute doesn't match the corresponding number of arguments, it will produce an error.
   * @param phi The base formula
   * @param m The map from schematic predicate symbols to lambda expressions Term(s) -> Formula [[LambdaTermFormula]].
   * @return phi[m]
   */
  def instantiatePredicateSchemas(phi: Formula, m: Map[SchematicVarOrPredLabel, LambdaTermFormula]): Formula = {
    require(m.forall { case (symbol, LambdaTermFormula(arguments, body)) => arguments.length == symbol.arity })
    phi match {
      case PredicateFormula(label, args) =>
        label match {
          case label: SchematicVarOrPredLabel if m.contains(label) => m(label)(args)
          case _ => phi
        }
      case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(instantiatePredicateSchemas(_, m)))
      case BinderFormula(label, bound, inner) =>
        val fv: Set[VariableLabel] = (m.flatMap { case (symbol, LambdaTermFormula(arguments, body)) => body.freeVariables }).toSet
        if (fv.contains(bound)) {
          val newBoundVariable = VariableLabel(freshId(fv.map(_.name), bound.name))
          val newInner = substituteVariablesInFormula(inner, Map(bound -> VariableTerm(newBoundVariable)))
          BinderFormula(label, newBoundVariable, instantiatePredicateSchemas(newInner, m))
        } else BinderFormula(label, bound, instantiatePredicateSchemas(inner, m))
    }
  }

  /**
   * Instantiate a schematic connector symbol in a formula, using higher-order instantiation.
   *
   * @param phi The base formula
   * @param m   The map from schematic function symbols to lambda expressions Formula(s) -> Formula [[LambdaFormulaFormula]].
   * @return phi[m]
   */
  def instantiateConnectorSchemas(phi: Formula, m: Map[SchematicConnectorLabel, LambdaFormulaFormula]): Formula = {
    require(m.forall { case (symbol, LambdaFormulaFormula(arguments, body)) => arguments.length == symbol.arity })
    phi match {
      case _: PredicateFormula => phi
      case ConnectorFormula(label, args) =>
        val newArgs = args.map(instantiateConnectorSchemas(_, m))
        label match {
          case label: SchematicConnectorLabel if m.contains(label) => m(label)(newArgs)
          case _ => ConnectorFormula(label, newArgs)
        }
      case BinderFormula(label, bound, inner) =>
        val fv: Set[VariableLabel] = (m.flatMap { case (symbol, LambdaFormulaFormula(arguments, body)) => body.freeVariables }).toSet
        if (fv.contains(bound)) {
          val newBoundVariable = VariableLabel(freshId(fv.map(_.name), bound.name))
          val newInner = substituteVariablesInFormula(inner, Map(bound -> VariableTerm(newBoundVariable)))
          BinderFormula(label, newBoundVariable, instantiateConnectorSchemas(newInner, m))
        } else BinderFormula(label, bound, instantiateConnectorSchemas(inner, m))
    }
  }

  /**
   * Instantiate a schematic connector symbol in a formula, using higher-order instantiation.
   *
   * @param phi The base formula
   * @param m   The map from schematic function symbols to lambda expressions Formula(s) -> Formula [[LambdaFormulaFormula]].
   * @return phi[m]
   */
  def instantiateSchemas(
      phi: Formula,
      mCon: Map[SchematicConnectorLabel, LambdaFormulaFormula],
      mPred: Map[SchematicVarOrPredLabel, LambdaTermFormula],
      mTerm: Map[SchematicTermLabel, LambdaTermTerm]
  ): Formula = {
    require(mCon.forall { case (symbol, LambdaFormulaFormula(arguments, body)) => arguments.length == symbol.arity })
    require(mPred.forall { case (symbol, LambdaTermFormula(arguments, body)) => arguments.length == symbol.arity })
    require(mTerm.forall { case (symbol, LambdaTermTerm(arguments, body)) => arguments.length == symbol.arity })
    phi match {
      case PredicateFormula(label, args) =>
        val newArgs = args.map(a => instantiateTermSchemasInTerm(a, mTerm))
        label match {
          case label: SchematicVarOrPredLabel if mPred.contains(label) => mPred(label)(newArgs)
          case _ => PredicateFormula(label, newArgs)
        }
      case ConnectorFormula(label, args) =>
        val newArgs = args.map(a => instantiateSchemas(a, mCon, mPred, mTerm))
        label match {
          case label: SchematicConnectorLabel if mCon.contains(label) => mCon(label)(newArgs)
          case _ => ConnectorFormula(label, newArgs)
        }
      case BinderFormula(label, bound, inner) =>
        val newmTerm = mTerm - bound
        val fv: Set[VariableLabel] =
          (mCon.flatMap { case (symbol, LambdaFormulaFormula(arguments, body)) => body.freeVariables }).toSet ++
            (mPred.flatMap { case (symbol, LambdaTermFormula(arguments, body)) => body.freeVariables }).toSet ++
            (mTerm.flatMap { case (symbol, LambdaTermTerm(arguments, body)) => body.freeVariables }).toSet
        if (fv.contains(bound)) {
          val newBoundVariable = VariableLabel(freshId(fv.map(_.name) ++ mTerm.keys.map(_.id), bound.name))
          val newInner = substituteVariablesInFormula(inner, Map(bound -> VariableTerm(newBoundVariable)))
          BinderFormula(label, newBoundVariable, instantiateSchemas(newInner, mCon, mPred, newmTerm))
        } else BinderFormula(label, bound, instantiateSchemas(inner, mCon, mPred, newmTerm))
    }
  }

}
