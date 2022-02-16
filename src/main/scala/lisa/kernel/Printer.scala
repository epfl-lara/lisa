package lisa.kernel

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SequentCalculus._
import lisa.kernel.proof.SCProof

/**
 * A set of methods to pretty-print kernel trees.
 */
object Printer {

    private def spaceSeparator(compact: Boolean): String = if(compact) "" else " "
    private def commaSeparator(compact: Boolean, symbol: String = ","): String = s"$symbol${spaceSeparator(compact)}"

    private def prettyParentheses(content: String): String = s"(${content})"

    private def prettyFunction(name: String, args: Seq[String], compact: Boolean, dropParentheses: Boolean = true): String = {
        if(dropParentheses && args.isEmpty) name else s"$name(${args.mkString(commaSeparator(compact))})"
    }

    private def prettyInfix(operator: String, left: String, right: String, compact: Boolean): String =
        Seq(left, operator, right).mkString(spaceSeparator(compact))

    // Special symbols that aren't defined in this theory
    private val (membership, subsetOf, sameCardinality) = (
        ConstantPredicateLabel("set_membership", 2),
        ConstantPredicateLabel("subset_of", 2),
        ConstantPredicateLabel("same_cardinality", 2)
    )
    private val (emptySet, unorderedPair, orderedPair, singleton, powerSet, unionSet) = (
        ConstantFunctionLabel("empty_set", 0),
        ConstantFunctionLabel("unordered_pair", 2),
        ConstantFunctionLabel("ordered_pair", 2),
        ConstantFunctionLabel("singleton", 1),
        ConstantFunctionLabel("power_set", 1),
        ConstantFunctionLabel("union", 1),
    )
    private val nonAtomicPredicates = Set(equality, membership, subsetOf, sameCardinality) // Predicates which require parentheses (for readability)

    private def prettyFormulaInternal(formula: Formula, isRightMost: Boolean, compact: Boolean): String = formula match {
        case PredicateFormula(label, args) => label match {
            case `equality` => args match {
                case Seq(l, r) => prettyInfix(label.id, prettyTerm(l), prettyTerm(r), compact)
                case _ => throw new Exception
            }
            case `membership` => args match {
                case Seq(l, r) => prettyInfix("∈", prettyTerm(l), prettyTerm(r), compact)
                case _ => throw new Exception
            }
            case `subsetOf` => args match {
                case Seq(l, r) => prettyInfix("⊆", prettyTerm(l), prettyTerm(r), compact)
                case _ => throw new Exception
            }
            case `sameCardinality` => args match {
                case Seq(l, r) => prettyInfix("~", prettyTerm(l), prettyTerm(r), compact)
                case _ => throw new Exception
            }
            case _ => prettyFunction(label.id, args.map(prettyTerm(_, compact)), compact)
        }
        case ConnectorFormula(label, args) =>
            (label, args) match {
                case (Neg, Seq(arg)) =>
                    val isAtomic = arg match {
                        case PredicateFormula(label, _) => !nonAtomicPredicates.contains(label)
                        case ConnectorFormula(Neg, _) => true
                        case _ => false
                    }
                    val bodyString = prettyFormulaInternal(arg, isRightMost, compact)
                    val bodyParenthesized = if(isAtomic) bodyString else prettyParentheses(bodyString)
                    s"${label.id}${bodyParenthesized}"
                case (binary @ (Implies | Iff | And | Or), Seq(l, r)) =>
                    val precedences: Map[ConnectorLabel, Int] = Map(
                        And -> 1,
                        Or -> 2,
                        Implies -> 3,
                        Iff -> 4,
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
                    val (leftString, rightString) = (prettyFormulaInternal(l, isLeftParentheses, compact), prettyFormulaInternal(r, isRightMost || isRightParentheses, compact))
                    val leftParenthesized = if(isLeftParentheses) prettyParentheses(leftString) else leftString
                    val rightParenthesized = if(isRightParentheses) prettyParentheses(rightString) else rightString
                    prettyInfix(label.id, leftParenthesized, rightParenthesized, compact)
                case (nary @ (And | Or), args) if args.nonEmpty =>
                    // Rewriting to match the above case; namely op(a) --> a, and op(a, ...rest) --> op(a, op(...rest))
                    // Empty args aren't allowed here
                    // Invariant: args.size > 2
                    if(args.sizeIs == 1) {
                        prettyFormulaInternal(args.head, isRightMost, compact)
                    } else {
                        prettyFormulaInternal(ConnectorFormula(nary, Seq(args.head, ConnectorFormula(nary, args.tail))), isRightMost, compact)
                    }
                case _ => prettyFunction(label.id, args.map(a => prettyFormulaInternal(a, isRightMost, compact)), compact)
            }
        case BinderFormula(label, bound, inner) =>
            def accumulateNested(f: Formula, acc: Seq[VariableLabel]): (Seq[VariableLabel], Formula) = f match {
                case BinderFormula(`label`, nestBound, nestInner) => accumulateNested(nestInner, nestBound +: acc)
                case _ => (acc, f)
            }
            val (bounds, innerNested) = accumulateNested(inner, Seq(bound))
            Seq(s"${label.id}${bounds.reverse.map(_.id).mkString(commaSeparator(compact))}.", prettyFormulaInternal(innerNested, true, compact)).mkString(spaceSeparator(compact))
    }

    /**
     * Returns a string representation of this formula. See also [[prettyTerm]].
     * Example output:
     * <pre>
     * ∀x, y. (∀z. (z ∈ x) ↔ (z ∈ y)) ↔ (x = y)
     * </pre>
     * @param formula the formula
     * @param compact whether spaces should be omitted between tokens
     * @return the string representation of this formula
     */
    def prettyFormula(formula: Formula, compact: Boolean = false): String = prettyFormulaInternal(formula, true, compact)

    /**
     * Returns a string representation of this term. See also [[prettyFormula]].
     * Example output:
     * <pre>
     * f({w, (x, y)}, z)
     * </pre>
     * @param term the term
     * @param compact whether spaces should be omitted between tokens
     * @return the string representation of this term
     */
    def prettyTerm(term: Term, compact: Boolean = false): String = term match {
        case VariableTerm(label) => label.id
        case FunctionTerm(label, args) =>
            label match {
                case `emptySet` => args match {
                    case Seq() => prettyFunction("∅", Seq.empty, compact, dropParentheses = true)
                    case _ => throw new Exception
                }
                case `unorderedPair` => args match {
                    case Seq(l, r) => s"{${Seq(l, r).map(prettyTerm(_, compact)).mkString(commaSeparator(compact))}}"
                    case _ => throw new Exception
                }
                case `orderedPair` => args match {
                    case Seq(l, r) => s"(${Seq(l, r).map(prettyTerm(_, compact)).mkString(commaSeparator(compact))})"
                    case _ => throw new Exception
                }
                case `singleton` => args match {
                    case Seq(s) => s"{${prettyTerm(s)}}"
                    case _ => throw new Exception
                }
                case `powerSet` => args match {
                    case Seq(s) => prettyFunction("P", Seq(prettyTerm(s)), compact)
                    case _ => throw new Exception
                }
                case `unionSet` => args match {
                    case Seq(s) => prettyFunction("U", Seq(prettyTerm(s)), compact)
                    case _ => throw new Exception
                }
                case _ => prettyFunction(label.id, args.map(prettyTerm(_, compact)), compact)
            }
    }

    /**
     * Returns a string representation of this sequent.
     * Example output:
     * <pre>
     * ⊢ ∀x, y. (∀z. (z ∈ x) ↔ (z ∈ y)) ↔ (x = y)
     * </pre>
     * @param sequent the sequent
     * @param compact whether spaces should be omitted between tokens
     * @return the string representation of this sequent
     */
    def prettySequent(sequent: Sequent, compact: Boolean = false): String = {
        def prettyFormulas(set: Set[Formula]): String = set.toSeq.map(prettyFormula(_, compact)).sorted.mkString(commaSeparator(compact, ";"))
        Seq(prettyFormulas(sequent.left), "⊢", prettyFormulas(sequent.right)).filter(_.nonEmpty).mkString(spaceSeparator(compact))
    }

    /**
     * Returns a string representation of this proof.
     * @param proof the proof
     * @param showError if set, marks that particular step in the proof (`->`) as an error
     * @return a string where each indented line corresponds to a step in the proof
     */
    def prettySCProof(proof: SCProof, showError: Option[(Seq[Int], String)] = None): String = {
        def computeMaxNumbering(proof: SCProof, level: Int, result: IndexedSeq[Int]): IndexedSeq[Int] = {
            val resultWithCurrent = result.updated(level, Math.max(proof.steps.size - 1, result(level)))
            proof.steps.collect { case sp: SCSubproof => sp }.foldLeft(resultWithCurrent)((acc, sp) => computeMaxNumbering(sp.sp, level + 1, if(acc.size <= level + 1) acc :+ 0 else acc))
        }
        val maxNumbering = computeMaxNumbering(proof, 0, IndexedSeq(0)) // The maximum value for each number column
        val maxNumberingLengths = maxNumbering.map(_.toString.length)
        val maxLevel = maxNumbering.size - 1

        def leftPadSpaces(v: Any, n: Int): String = {
            val s = String.valueOf(v)
            if(s.length < n) (" " * (n - s.length)) + s else s
        }
        def rightPadSpaces(v: Any, n: Int): String = {
            val s = String.valueOf(v)
            if(s.length < n) s + (" " * (n - s.length)) else s
        }
        def prettySCProofRecursive(proof: SCProof, level: Int, tree: IndexedSeq[Int], topMostIndices: IndexedSeq[Int]): Seq[(Boolean, String, String, String)] = {
            val printedImports = proof.imports.zipWithIndex.reverse.flatMap { case (imp, i) =>
                val currentTree = tree :+ (-i-1)
                val showErrorForLine = showError.exists((position, reason) => currentTree.startsWith(position) && currentTree.drop(position.size).forall(_ == 0))
                val prefix = (Seq.fill(level - topMostIndices.size)(None) ++  Seq.fill(topMostIndices.size)(None) :+ Some(-i-1)) ++ Seq.fill(maxLevel - level)(None)
                val prefixString = prefix.map(_.map(_.toString).getOrElse("")).zipWithIndex.map { case (v, i1) => leftPadSpaces(v, maxNumberingLengths(i1)) }.mkString(" ")
                def pretty(stepName: String, topSteps: Int*): (Boolean, String, String, String) =
                    (
                        showErrorForLine,
                        prefixString,
                        Seq(stepName, topSteps.mkString(commaSeparator(compact = false))).filter(_.nonEmpty).mkString(" "),
                        prettySequent(imp)
                    )

                Seq(pretty("Import", 0))
            }
            printedImports ++ proof.steps.zipWithIndex.flatMap { case (step, i) =>
                val currentTree = tree :+ i
                val showErrorForLine = showError.exists((position, reason) => currentTree.startsWith(position) && currentTree.drop(position.size).forall(_ == 0))
                val prefix = (Seq.fill(level - topMostIndices.size)(None) ++  Seq.fill(topMostIndices.size)(None) :+ Some(i)) ++ Seq.fill(maxLevel - level)(None)
                val prefixString = prefix.map(_.map(_.toString).getOrElse("")).zipWithIndex.map { case (v, i1) => leftPadSpaces(v, maxNumberingLengths(i1)) }.mkString(" ")
                def pretty(stepName: String, topSteps: Int*): (Boolean, String, String, String) =
                    (
                        showErrorForLine,
                        prefixString,
                        Seq(stepName, topSteps.mkString(commaSeparator(compact = false))).filter(_.nonEmpty).mkString(" "),
                        prettySequent(step.bot)
                    )
                step match {
                    case sp @ SCSubproof(_, _, true) => pretty("Subproof", sp.premises*) +: prettySCProofRecursive(sp.sp, level + 1, currentTree, (if(i == 0) topMostIndices else IndexedSeq.empty) :+ i)
                    case other =>
                        val line = other match {
                            case Rewrite(_, t1) => pretty("Rewrite", t1)
                            case Hypothesis(_, _) => pretty("Hypo.")
                            case Cut(_, t1, t2, _) => pretty("Cut", t1, t2)
                            case LeftAnd(_, t1, _, _) => pretty("Left ∧", t1)
                            case LeftNot(_, t1, _) => pretty("Left ¬", t1)
                            case RightOr(_, t1, _, _) => pretty("Right ∨", t1)
                            case RightNot(_, t1, _) => pretty("Right ¬", t1)
                            case LeftExists(_, t1, _, _) => pretty("Left ∃", t1)
                            case LeftForall(_, t1, _, _, _) => pretty("Left ∀", t1)
                            case LeftOr(_, l, _) => pretty("Left ∨", l*)
                            case RightExists(_, t1, _, _, _) => pretty("Right ∃", t1)
                            case RightForall(_, t1, _, _) => pretty("Right ∀", t1)
                            case RightAnd(_, l, _) => pretty("Right ∧", l*)
                            case RightIff(_, t1, t2, _, _) => pretty("Right ↔", t1, t2)
                            case RightImplies(_, t1, _, _) => pretty("Right →", t1)
                            case Weakening(_, t1) => pretty("Weakening", t1)
                            case LeftImplies(_, t1, t2, _, _) => pretty("Left →", t1, t2)
                            case LeftIff(_, t1, _, _) => pretty("Left ↔", t1)
                            case LeftRefl(_, t1, _) => pretty("L. Refl", t1)
                            case RightRefl(_, _) => pretty("R. Refl")
                            case LeftSubstEq(_, t1, _, _, _, _) => pretty("L. SubstEq", t1)
                            case RightSubstEq(_, t1, _, _, _, _) => pretty("R. SubstEq", t1)
                            case LeftSubstIff(_, t1, _, _, _, _) => pretty("L. SubstIff", t1)
                            case RightSubstIff(_, t1, _, _, _, _) => pretty("R. SubstIff", t1)
                            case InstantiateSchematicFunction(_, t1, _, _, _) => pretty("?Fun Instantiation", t1)
                            case InstantiateSchematicPredicate(_, t1, _, _, _) => pretty("?Pred Instantiation", t1)
                            case SCSubproof(_, _, false) => pretty("SCSubproof (hidden)")
                            case other => throw new Exception(s"No available method to print this proof step, consider updating Printer.scala\n$other")
                        }
                        Seq(line)
                }
            }
        }


        val marker = "->"

        val lines = prettySCProofRecursive(proof, 0, IndexedSeq.empty, IndexedSeq.empty)
        val maxStepNameLength = lines.map { case (_, _, stepName, _) => stepName.length }.maxOption.getOrElse(0)
        lines.map {
            case (isMarked, indices, stepName, sequent) =>
                val suffix = Seq(indices, rightPadSpaces(stepName, maxStepNameLength), sequent)
                val full = if(showError.nonEmpty) (if(isMarked) marker else leftPadSpaces("", marker.length)) +: suffix else suffix
                full.mkString(" ")
        }.mkString("\n") + (if (showError.nonEmpty) s"\nProof checker has reported error at line ${showError.get._1}: ${showError.get._2}" else "")
    }

}
