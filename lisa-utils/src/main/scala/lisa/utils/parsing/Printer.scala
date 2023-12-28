package lisa.utils.parsing

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofCheckerJudgement
import lisa.kernel.proof.SCProofCheckerJudgement.*
import lisa.kernel.proof.SequentCalculus.*

val FOLPrinter = Printer(FOLParser)

/**
 * A set of methods to pretty-print kernel trees.
 */
class Printer(parser: Parser) {

  private def spaceSeparator(compact: Boolean): String = if (compact) "" else " "

  private def commaSeparator(compact: Boolean, symbol: String = ","): String = s"$symbol${spaceSeparator(compact)}"

  /**
   * Returns a string representation of this formula. See also [[prettyTerm]].
   * Example output:
   * <pre>
   * ∀x, y. (∀z. (z ∈ x) ⇔ (z ∈ y)) ⇔ (x = y)
   * </pre>
   *
   * @param formula the formula
   * @param compact whether spaces should be omitted between tokens
   * @return the string representation of this formula
   */
  def prettyFormula(formula: Formula, compact: Boolean = false): String = parser.printFormula(formula)

  /**
   * Returns a string representation of this term. See also [[prettyFormula]].
   * Example output:
   * <pre>
   * f({w, (x, y)}, z)
   * </pre>
   *
   * @param term    the term
   * @param compact whether spaces should be omitted between tokens
   * @return the string representation of this term
   */
  def prettyTerm(term: Term, compact: Boolean = false): String = parser.printTerm(term)

  /**
   * Returns a string representation of this sequent.
   * Example output:
   * <pre>
   * ⊢ ∀x, y. (∀z. (z ∈ x) ⇔ (z ∈ y)) ⇔ (x = y)
   * </pre>
   *
   * @param sequent the sequent
   * @param compact whether spaces should be omitted between tokens
   * @return the string representation of this sequent
   */
  def prettySequent(sequent: Sequent, compact: Boolean = false): String = parser.printSequent(sequent)

  /**
   * Returns a string representation of this proof.
   *
   * @param proof     the proof
   * @param judgement optionally provide a proof checking judgement that will mark a particular step in the proof
   *                  (`->`) as an error. The proof is considered to be valid by default
   * @return a string where each indented line corresponds to a step in the proof
   */
  def prettySCProof(judgement: SCProofCheckerJudgement, forceDisplaySubproofs: Boolean = false): String = {
    val proof = judgement.proof
    def computeMaxNumberingLengths(proof: SCProof, level: Int, result: IndexedSeq[Int]): IndexedSeq[Int] = {
      val resultWithCurrent = result.updated(
        level,
        (Seq((proof.steps.size - 1).toString.length, result(level)) ++ (if (proof.imports.nonEmpty) Seq((-proof.imports.size).toString.length) else Seq.empty)).max
      )
      proof.steps.collect { case sp: SCSubproof => sp }.foldLeft(resultWithCurrent)((acc, sp) => computeMaxNumberingLengths(sp.sp, level + 1, if (acc.size <= level + 1) acc :+ 0 else acc))
    }

    val maxNumberingLengths = computeMaxNumberingLengths(proof, 0, IndexedSeq(0)) // The maximum value for each number column
    val maxLevel = maxNumberingLengths.size - 1

    def leftPadSpaces(v: Any, n: Int): String = {
      val s = String.valueOf(v)
      if (s.length < n) (" " * (n - s.length)) + s else s
    }

    def rightPadSpaces(v: Any, n: Int): String = {
      val s = String.valueOf(v)
      if (s.length < n) s + (" " * (n - s.length)) else s
    }

    def prettySCProofRecursive(proof: SCProof, level: Int, tree: IndexedSeq[Int], topMostIndices: IndexedSeq[Int]): Seq[(Boolean, String, String, String)] = {
      val printedImports = proof.imports.zipWithIndex.reverse.flatMap { case (imp, i) =>
        val currentTree = tree :+ (-i - 1)
        val showErrorForLine = judgement match {
          case SCValidProof(_, _) => false
          case SCInvalidProof(proof, position, _) => currentTree.startsWith(position) && currentTree.drop(position.size).forall(_ == 0)
        }
        val prefix = (Seq.fill(level - topMostIndices.size)(None) ++ Seq.fill(topMostIndices.size)(None) :+ Some(-i - 1)) ++ Seq.fill(maxLevel - level)(None)
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
        val showErrorForLine = judgement match {
          case SCValidProof(_, _) => false
          case SCInvalidProof(proof, position, _) => currentTree.startsWith(position) && currentTree.drop(position.size).forall(_ == 0)
        }
        val prefix = (Seq.fill(level - topMostIndices.size)(None) ++ Seq.fill(topMostIndices.size)(None) :+ Some(i)) ++ Seq.fill(maxLevel - level)(None)
        val prefixString = prefix.map(_.map(_.toString).getOrElse("")).zipWithIndex.map { case (v, i1) => leftPadSpaces(v, maxNumberingLengths(i1)) }.mkString(" ")

        def pretty(stepName: String, topSteps: Int*): (Boolean, String, String, String) =
          (
            showErrorForLine,
            prefixString,
            Seq(stepName, topSteps.mkString(commaSeparator(compact = false))).filter(_.nonEmpty).mkString(" "),
            prettySequent(step.bot)
          )

        step match {
          case sp @ SCSubproof(_, _) =>
            pretty("Subproof", sp.premises*) +: prettySCProofRecursive(sp.sp, level + 1, currentTree, (if (i == 0) topMostIndices else IndexedSeq.empty) :+ i)
          case other =>
            val line = other match {
              case Restate(_, t1) => pretty("Rewrite", t1)
              case RestateTrue(_) => pretty("RewriteTrue")
              case Hypothesis(_, _) => pretty("Hypo.")
              case Cut(_, t1, t2, _) => pretty("Cut", t1, t2)
              case LeftAnd(_, t1, _, _) => pretty("Left ∧", t1)
              case LeftNot(_, t1, _) => pretty("Left ¬", t1)
              case RightOr(_, t1, _, _) => pretty("Right ∨", t1)
              case RightNot(_, t1, _) => pretty("Right ¬", t1)
              case LeftExists(_, t1, _, _) => pretty("Left ∃", t1)
              case LeftForall(_, t1, _, _, _) => pretty("Left ∀", t1)
              case LeftExistsOne(_, t1, _, _) => pretty("Left ∃!", t1)
              case LeftOr(_, l, _) => pretty("Left ∨", l*)
              case RightExists(_, t1, _, _, _) => pretty("Right ∃", t1)
              case RightForall(_, t1, _, _) => pretty("Right ∀", t1)
              case RightExistsOne(_, t1, _, _) => pretty("Right ∃!", t1)
              case RightAnd(_, l, _) => pretty("Right ∧", l*)
              case RightIff(_, t1, t2, _, _) => pretty("Right ⇔", t1, t2)
              case RightImplies(_, t1, _, _) => pretty("Right ⇒", t1)
              case Weakening(_, t1) => pretty("Weakening", t1)
              case LeftImplies(_, t1, t2, _, _) => pretty("Left ⇒", t1, t2)
              case LeftIff(_, t1, _, _) => pretty("Left ⇔", t1)
              case LeftRefl(_, t1, _) => pretty("L. Refl", t1)
              case RightRefl(_, _) => pretty("R. Refl")
              case LeftSubstEq(_, t1, _, _) => pretty("L. SubstEq", t1)
              case RightSubstEq(_, t1, _, _) => pretty("R. SubstEq", t1)
              case LeftSubstIff(_, t1, _, _) => pretty("L. SubstIff", t1)
              case RightSubstIff(_, t1, _, _) => pretty("R. SubstIff", t1)
              case InstSchema(_, t1, _, _, _) => pretty("Schema Instantiation", t1)
              case Sorry(_) => pretty("Sorry")
              case SCSubproof(_, _) => throw UnreachableException
            }
            Seq(line)
        }
      }
    }

    val marker = "->"

    val lines = prettySCProofRecursive(proof, 0, IndexedSeq.empty, IndexedSeq.empty)
    val maxStepNameLength = lines.map { case (_, _, stepName, _) => stepName.length }.maxOption.getOrElse(0)
    lines
      .map { case (isMarked, indices, stepName, sequent) =>
        val suffix = Seq(indices, rightPadSpaces(stepName, maxStepNameLength), sequent)
        val full = if (!judgement.isValid) (if (isMarked) marker else leftPadSpaces("", marker.length)) +: suffix else suffix
        full.mkString(" ")
      }
      .mkString("\n") + (judgement match {
      case SCValidProof(_, _) => ""
      case SCInvalidProof(proof, path, message) => s"\nProof checker has reported an error at line ${path.mkString(".")}: $message"
    })
  }

  def prettySCProof(proof: SCProof): String = prettySCProof(SCValidProof(proof), false)
}
