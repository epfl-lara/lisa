package lisa.front.printer

import lisa.front.fol.FOL.*
import lisa.front.parser.FrontSymbols
import lisa.front.proof.Proof.*
import lisa.front.printer.FrontPrintNode.*
import lisa.front.printer.FrontPrintParameters
import lisa.front.theory.SetTheory

/**
 * A set of methods to positioned-print kernel trees.
 */
object FrontPositionedPrinter {

  private val rName = "[a-zA-Z_][a-zA-Z0-9_]*".r
  private def isNamePrintable(name: String): Boolean = rName.matches(name)

  private def isTermPrintableInternal(term: Term, variables: Set[String]): Boolean = term match {
    case VariableTerm(label) =>
      assert(variables.contains(label.id)) // By assumption, thus `isNamePrintable` is true
      true
    case Term(label, args) =>
      val isLabelPrintable = label match {
        case SchematicTermLabel(id, _) => !variables.contains(id)
        case _ => true
      }
      isNamePrintable(label.id) && isLabelPrintable && args.forall(isTermPrintableInternal(_, variables))
  }

  private def isTermPrintable(term: Term, freeVariables: Set[VariableLabel]): Boolean =
    freeVariables.map(_.id).forall(isNamePrintable) && isWellFormed(term) && isTermPrintableInternal(term, freeVariables.map(_.id))

  private def isFormulaPrintableInternal(formula: Formula, variables: Set[String]): Boolean = formula match {
    case PredicateFormula(label, args) =>
      (!label.isInstanceOf[SchematicLabelType] || isNamePrintable(label.id)) && args.forall(isTermPrintableInternal(_, variables))
    case ConnectorFormula(label, args) =>
      (!label.isInstanceOf[SchematicLabelType] || isNamePrintable(label.id)) && args.forall(isFormulaPrintableInternal(_, variables))
    case BinderFormula(label, bound, inner) =>
      isNamePrintable(bound.id) && !variables.contains(bound.id) && isFormulaPrintableInternal(inner, variables + bound.id)
  }

  private def isFormulaPrintable(formula: Formula, freeVariables: Set[VariableLabel]): Boolean =
    freeVariables.map(_.id).forall(isNamePrintable) && isWellFormed(formula) && isFormulaPrintableInternal(formula, freeVariables.map(_.id))


  private def mkSep(items: FrontPrintNode*)(separator: FrontLeaf): IndexedSeq[FrontPrintNode] = {
    val nodes = items match {
      case head +: tail =>
        head +: tail.flatMap(Seq(separator, _))
      case other => other
    }
    nodes.toIndexedSeq
  }

  private def spaceSeparator(using p: FrontPrintParameters): String = if(p.compact) "" else " "
  private def commaSeparator(separator: String)(using FrontPrintParameters): String = s"$separator$spaceSeparator"
  private def commaSeparator(using p: FrontPrintParameters): String = commaSeparator(p.s.Comma)

  private def prettyName(name: String)(using p: FrontPrintParameters): String =
    if(p.symbols == FrontPrintStyle.Latex && p.compact) s"{$name}" else name
  private def prettyLabel(label: LabelType, double: Boolean = false)(using p: FrontPrintParameters): String = {
    val (result, mustWrap) = label match {
      case _: SchematicLabelType =>
        val s = s"${if(double) p.s.QuestionMark else ""}${p.s.QuestionMark}${label.id}"
        (s, true)
      case _ => (label.id, false)
    }
    if((mustWrap && p.symbols == FrontPrintStyle.Latex) || (p.symbols == FrontPrintStyle.Latex && p.compact)) s"{$result}" else result
  }

  private def positionedParentheses(content: FrontPrintNode)(using p: FrontPrintParameters): IndexedSeq[FrontPrintNode] =
    IndexedSeq(p.s.ParenthesisOpen, content, p.s.ParenthesisClose)

  private def positionedFunction(name: String, args: Seq[FrontBranch], dropParentheses: Boolean = true)(using p: FrontPrintParameters): FrontBranch = {
    if(dropParentheses && args.isEmpty)
      FrontBranch(name)
    else
      FrontBranch(FrontLeaf(s"$name${p.s.ParenthesisOpen}") +: mkSep(args*)(commaSeparator) :+ FrontLeaf(p.s.ParenthesisClose))
  }

  private def positionedInfix(operator: String, left: FrontPrintNode, right: FrontPrintNode)(using FrontPrintParameters): FrontBranch =
    FrontBranch(mkSep(left, operator, right)(spaceSeparator))
  private def positionedInfix(operator: FrontPrintNode, left: IndexedSeq[FrontPrintNode], right: IndexedSeq[FrontPrintNode])(using FrontPrintParameters): FrontBranch =
    FrontBranch(left ++ Seq(FrontLeaf(spaceSeparator)) ++ IndexedSeq(operator) ++ Seq(FrontLeaf(spaceSeparator)) ++ right)

  // Special symbols that aren't defined in this theory
  private val (membership, subsetOf, sameCardinality) = (
    SetTheory.membership,
    SetTheory.subset,
    SetTheory.sameCardinality
  )
  private val (emptySet, unorderedPair, orderedPair, singleton, powerSet, unionSet) = (
    SetTheory.emptySet,
    SetTheory.unorderedPairSet,
    ConstantFunctionLabel[2]("ordered_pair"),
    SetTheory.singletonSet,
    SetTheory.powerSet,
    SetTheory.unionSet,
  )
  private val nonAtomicPredicates = Set[PredicateLabel[?]](equality, membership, subsetOf, sameCardinality) // Predicates which require parentheses (for readability)

  private def positionedFormulaInternal(formula: Formula, isRightMost: Boolean)(using p: FrontPrintParameters): FrontBranch = formula match {
    case PredicateFormula(label, args) => label match {
      case `equality` => args match {
        case Seq(l, r) => positionedInfix(p.s.Equal, positionedTermInternal(l), positionedTermInternal(r))
        case _ => throw new Error
      }
      case `membership` => args match {
        case Seq(l, r) => positionedInfix(p.s.Membership, positionedTermInternal(l), positionedTermInternal(r))
        case _ => throw new Error
      }
      case `subsetOf` => args match {
        case Seq(l, r) => positionedInfix(p.s.Subset, positionedTermInternal(l), positionedTermInternal(r))
        case _ => throw new Error
      }
      case `sameCardinality` => args match {
        case Seq(l, r) => positionedInfix(p.s.Tilde, positionedTermInternal(l), positionedTermInternal(r))
        case _ => throw new Error
      }
      case _ =>
        positionedFunction(prettyLabel(label), args.map(positionedTermInternal(_)))
    }
    case ConnectorFormula(label, args) =>
      (label, args) match {
        case (`neg`, Seq(arg)) =>
          val isAtomic = arg match {
            case PredicateFormula(label, _) => !nonAtomicPredicates.contains(label)
            case ConnectorFormula(`neg`, _) => true
            case _ => false
          }
          val bodyString = positionedFormulaInternal(arg, isRightMost)
          val bodyParenthesized = if(isAtomic) IndexedSeq(bodyString) else positionedParentheses(bodyString)
          FrontBranch(FrontLeaf(p.s.Exclamation) +: bodyParenthesized)
        case (binary @ (`implies` | `iff` | `and` | `or`), Seq(l, r)) =>
          val precedences: Map[ConnectorLabel[?], Int] = Map(
            and -> 1,
            or -> 2,
            implies -> 3,
            iff -> 4,
          )
          val symbols: Map[ConnectorLabel[?], String] = Map(
            and -> p.s.And,
            or -> p.s.Or,
            implies -> p.s.Implies,
            iff -> p.s.Iff,
          )
          val precedence = precedences(binary)
          val isLeftParentheses = l match {
            case _: BinderFormula => true
            case PredicateFormula(leftLabel, _) => nonAtomicPredicates.contains(leftLabel)
            case ConnectorFormula(leftLabel, _) => precedences.get(leftLabel).exists(_ >= precedence)
          }
          val isRightParentheses = r match {
            case _: BinderFormula => !isRightMost
            case PredicateFormula(leftLabel, _) => nonAtomicPredicates.contains(leftLabel)
            case ConnectorFormula(rightLabel, _) => precedences.get(rightLabel).exists(_ > precedence)
          }
          val (leftString, rightString) = (positionedFormulaInternal(l, isLeftParentheses), positionedFormulaInternal(r, isRightMost || isRightParentheses))
          val leftParenthesized = if(isLeftParentheses) positionedParentheses(leftString) else IndexedSeq(leftString)
          val rightParenthesized = if(isRightParentheses) positionedParentheses(rightString) else IndexedSeq(rightString)
          positionedInfix(symbols(label), leftParenthesized, rightParenthesized)
        case (nary @ (`and` | `or`), args) if args.nonEmpty =>
          // FIXME wrong indexing if we do that
          // Rewriting to match the above case; namely op(a) --> a, and op(a, ...rest) --> op(a, op(...rest))
          // Empty args aren't allowed here
          // Invariant: args.size > 2
          if(args.sizeIs == 1) {
            positionedFormulaInternal(args.head, isRightMost)
          } else {
            positionedFormulaInternal(ConnectorFormula.unsafe(nary, Seq(args.head, ConnectorFormula.unsafe(nary, args.tail))), isRightMost)
          }
        case _ => positionedFunction(prettyLabel(label, double = true), args.map(a => positionedFormulaInternal(a, isRightMost)))
      }
    case BinderFormula(label, bound, inner) =>
      val symbols: Map[BinderLabel, String] = Map(
        forall -> p.s.Forall,
        exists -> p.s.Exists,
        existsOne -> p.s.ExistsOne,
      )
      def accumulateNested(f: Formula, acc: Seq[VariableLabel]): (Seq[VariableLabel], Formula) = f match {
        case BinderFormula(`label`, nestBound, nestInner) => accumulateNested(nestInner, nestBound +: acc)
        case _ => (acc, f)
      }
      val (bounds, innerNested) = accumulateNested(inner, Seq(bound))

      val innerTree = FrontBranch(mkSep(
        FrontLeaf(s"${symbols(label)}${if(p.symbols == FrontPrintStyle.Ascii || p.symbols == FrontPrintStyle.Latex) " " else ""}${bounds.reverse.map(_.id).mkString(commaSeparator)}${p.s.Dot}"),
        positionedFormulaInternal(innerNested, true),
      )(spaceSeparator))
      bounds.tail.foldLeft(innerTree)((acc, _) => FrontBranch(acc))
  }

  private def positionedExpression(freeVariables: Set[VariableLabel], expression: FrontBranch)(using p: FrontPrintParameters): FrontBranch = {
    FrontBranch(expression.children)
  }

  /**
   * Returns a string representation of this formula. See also [[positionedTerm]].
   * Example output:
   * <pre>
   * ∀x, y. (∀z. (z ∈ x) ↔ (z ∈ y)) ↔ (x = y)
   * </pre>
   * @param formula the formula
   * @param ascii whether it should be printed in ASCII or unicode
   * @param compact whether spaces should be omitted between tokens
   * @return the string representation of this formula
   */
  def positionedFormula(formula: Formula, symbols: FrontPrintStyle = FrontPrintStyle.Unicode, compact: Boolean = false, strict: Boolean = false): FrontBranch = {
    given FrontPrintParameters = FrontPrintParameters(symbols, compact)
    val f = positionedFormulaInternal(formula, true)
    val freeVariables = freeVariablesOf(formula)
    if(strict) {
      require(isFormulaPrintable(formula, freeVariables))
    }
    positionedExpression(freeVariables, f)
  }

  def prettyFormula(formula: Formula, symbols: FrontPrintStyle = FrontPrintStyle.Unicode, compact: Boolean = false): String =
    positionedFormula(formula, symbols, compact).print

  private def positionedTermInternal(term: Term)(using p: FrontPrintParameters): FrontBranch = term match {
    //case VariableTerm(label) => FrontBranch(prettyName(label.id))
    case Term(label, args) =>
      label match {
        case `emptySet` => args match {
          case Seq() => positionedFunction(p.s.EmptySet, Seq.empty, dropParentheses = true)
          case _ => throw new Error
        }
        case `unorderedPair` => args match {
          case Seq(l, r) => FrontBranch(p.s.CurlyBracketOpen, positionedTermInternal(l), commaSeparator, positionedTermInternal(r), p.s.CurlyBracketClose)
          case _ => throw new Error
        }
        case `orderedPair` => args match {
          case Seq(l, r) => FrontBranch(p.s.ParenthesisOpen, positionedTermInternal(l), commaSeparator, positionedTermInternal(r), p.s.ParenthesisClose)
          case _ => throw new Error
        }
        case `singleton` => args match {
          case Seq(s) => FrontBranch(p.s.CurlyBracketOpen, positionedTermInternal(s), p.s.CurlyBracketClose)
          case _ => throw new Error
        }
        case `powerSet` => args match {
          case Seq(s) => positionedFunction(p.s.PowerSet, Seq(positionedTermInternal(s)))
          case _ => throw new Error
        }
        case `unionSet` => args match {
          case Seq(s) => positionedFunction(p.s.UnionSet, Seq(positionedTermInternal(s)))
          case _ => throw new Error
        }
        case _ =>
          positionedFunction(prettyLabel(label), args.map(positionedTermInternal(_)))
      }
  }

  /**
   * Returns a string representation of this term. See also [[positionedFormula]].
   * Example output:
   * <pre>
   * f({w, (x, y)}, z)
   * </pre>
   * @param term the term
   * @param ascii whether it should be printed in ASCII or unicode
   * @param compact whether spaces should be omitted between tokens
   * @return the string representation of this term
   */
  def positionedTerm(term: Term, symbols: FrontPrintStyle = FrontPrintStyle.Unicode, compact: Boolean = false, strict: Boolean = false): FrontBranch = {
    if(strict) {
      require(isTermPrintable(term, Set.empty)) // Trivially true
    }
    positionedTermInternal(term)(using FrontPrintParameters(symbols, compact))
  }

  def prettyTerm(term: Term, symbols: FrontPrintStyle = FrontPrintStyle.Unicode, compact: Boolean = false, strict: Boolean = false): String =
    positionedTerm(term, symbols, compact, strict).print

  private def positionedSequentBase(sequent: SequentBase, symbols: FrontPrintStyle = FrontPrintStyle.Unicode, compact: Boolean = false, strict: Boolean = false): FrontBranch = {
    given p: FrontPrintParameters = FrontPrintParameters(symbols, compact)
    val (partialLeft, partialRight) = sequent match {
      case _: Sequent => (false, false)
      case PartialSequent(_, _, partialLeft, partialRight) => (partialLeft, partialRight)
    }
    def positionedEllipsis(display: Boolean): Seq[FrontPrintNode] = if(display) Seq(p.s.Ellipsis) else Seq.empty
    def sortedFormulas(seq: IndexedSeq[Formula]): IndexedSeq[FrontPrintNode] =
      seq.map(positionedFormulaInternal(_, true)).sortBy(_.print)
    val (lhs, rhs) = (
      mkSep((positionedEllipsis(partialLeft) ++ sortedFormulas(sequent.left))*)(commaSeparator(p.s.Semicolon)),
      mkSep((sortedFormulas(sequent.right) ++ positionedEllipsis(partialRight))*)(commaSeparator(p.s.Semicolon))
    )
    def spaceFor(seq: IndexedSeq[FrontPrintNode]): Seq[FrontPrintNode] = if(seq.nonEmpty) Seq(spaceSeparator) else Seq.empty
    val expression = FrontBranch((
        lhs ++ spaceFor(lhs) ++ Seq(FrontLeaf(p.s.Turnstile)) ++ spaceFor(rhs) ++ rhs
      )*)
    val freeVariables = freeVariablesOfSequent(sequent)
    if(strict) {
      require(sequent.formulas.forall(isFormulaPrintable(_, freeVariables)))
    }
    positionedExpression(freeVariables, expression)
  }

  /**
   * Returns a string representation of this sequent.
   * Example output:
   * <pre>
   * ⊢ ∀x, y. (∀z. (z ∈ x) ↔ (z ∈ y)) ↔ (x = y)
   * </pre>
   * @param sequent the sequent
   * @param ascii whether it should be printed in ASCII or unicode
   * @param compact whether spaces should be omitted between tokens
   * @return the string representation of this sequent
   */
  def positionedSequent(sequent: Sequent, symbols: FrontPrintStyle = FrontPrintStyle.Unicode, compact: Boolean = false, strict: Boolean = false): FrontBranch =
    positionedSequentBase(sequent, symbols, compact, strict)

  def prettySequent(sequent: Sequent, symbols: FrontPrintStyle = FrontPrintStyle.Unicode, compact: Boolean = false, strict: Boolean = false): String =
    positionedSequent(sequent, symbols, compact, strict).print

  def positionedPartialSequent(sequent: PartialSequent, symbols: FrontPrintStyle = FrontPrintStyle.Unicode, compact: Boolean = false, strict: Boolean = false): FrontBranch =
    positionedSequentBase(sequent, symbols, compact, strict)

  def prettyPartialSequent(sequent: PartialSequent, symbols: FrontPrintStyle = FrontPrintStyle.Unicode, compact: Boolean = false, strict: Boolean = false): String =
    positionedPartialSequent(sequent, symbols, compact, strict).print
}
