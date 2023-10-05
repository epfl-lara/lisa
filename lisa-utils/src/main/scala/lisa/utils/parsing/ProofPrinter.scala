package lisa.utils.parsing

import lisa.kernel.proof.SCProofCheckerJudgement
import lisa.prooflib.BasicStepTactic.SUBPROOF
import lisa.prooflib.Library
import lisa.prooflib.*
import lisa.utils.*

//temporary - get merged wit regular printer in time
object ProofPrinter {

  private def spaceSeparator(compact: Boolean): String = if (compact) "" else " "

  private def commaSeparator(compact: Boolean, symbol: String = ","): String = s"$symbol${spaceSeparator(compact)}"

  private def prettyProofLines(printedProof: Library#Proof, error: Option[(IndexedSeq[Int], String)]): Seq[String] = {
    def computeMaxNumberingLengths(proof: Library#Proof, level: Int, result: IndexedSeq[Int]): IndexedSeq[Int] = {
      val resultWithCurrent = result.updated(
        level,
        (Seq((proof.getSteps.size - 1).toString.length, result(level)) ++ (if (proof.getImports.nonEmpty) Seq((-proof.getImports.size).toString.length) else Seq.empty)).max
      )
      proof.getSteps
        .collect { case ps: proof.ProofStep if ps.tactic.isInstanceOf[SUBPROOF] => ps.tactic.asInstanceOf[SUBPROOF] }
        .foldLeft(resultWithCurrent)((acc, sp) => computeMaxNumberingLengths(sp.iProof, level + 1, if (acc.size <= level + 1) acc :+ 0 else acc))
    }

    val maxNumberingLengths = computeMaxNumberingLengths(printedProof, 0, IndexedSeq(0)) // The maximum value for each number column
    val maxLevel = maxNumberingLengths.size - 1

    def leftPadSpaces(v: Any, n: Int): String = {
      val s = String.valueOf(v)
      if (s.length < n) (" " * (n - s.length)) + s else s
    }

    def rightPadSpaces(v: Any, n: Int): String = {
      val s = String.valueOf(v)
      if (s.length < n) s + (" " * (n - s.length)) else s
    }

    def prettyProofRecursive(printedProof: Library#Proof, level: Int, tree: IndexedSeq[Int], topMostIndices: IndexedSeq[Int]): Seq[(Boolean, String, String, String)] = {
      val imports = printedProof.getImports
      val steps = printedProof.getSteps
      val printedImports = imports.zipWithIndex.reverse.flatMap { case (imp, i) =>
        val currentTree = tree :+ (-i - 1)

        val showErrorForLine: Boolean = error match {
          case None => false
          case Some((position, message)) => currentTree.startsWith(position) && currentTree.drop(position.size).forall(_ == 0)
        }

        val prefix = (Seq.fill(level - topMostIndices.size)(None) ++ Seq.fill(topMostIndices.size)(None) :+ Some(-i - 1)) ++ Seq.fill(maxLevel - level)(None)
        val prefixString = prefix.map(_.map(_.toString).getOrElse("")).zipWithIndex.map { case (v, i1) => leftPadSpaces(v, maxNumberingLengths(i1)) }.mkString(" ")

        def pretty(stepName: String, topSteps: Int*): (Boolean, String, String, String) =
          (
            showErrorForLine,
            prefixString,
            Seq(stepName, topSteps.mkString(commaSeparator(compact = false))).filter(_.nonEmpty).mkString(" "),
            imp._2.toString()
          )

        Seq(pretty("Import", 0))
      }
      printedImports ++ steps.zipWithIndex.flatMap { case (step, i) =>
        val currentTree = tree :+ i
        val showErrorForLine: Boolean = error match {
          case None => false
          case Some((position, message)) => currentTree.startsWith(position) && currentTree.drop(position.size).forall(_ == 0)
        }
        val prefix = (Seq.fill(level - topMostIndices.size)(None) ++ Seq.fill(topMostIndices.size)(None) :+ Some(i)) ++ Seq.fill(maxLevel - level)(None)
        val prefixString = prefix.map(_.map(_.toString).getOrElse("")).zipWithIndex.map { case (v, i1) => leftPadSpaces(v, maxNumberingLengths(i1)) }.mkString(" ")

        def pretty(stepName: String, topSteps: Int*): (Boolean, String, String, String) =
          (
            showErrorForLine,
            prefixString,
            Seq(stepName, topSteps.mkString(commaSeparator(compact = false))).filter(_.nonEmpty).mkString(" "),
            step.bot.toString()
          )

        step.tactic match {
          case sp: SUBPROOF =>
            val topSteps: Seq[Int] = sp.premises.map((f: sp.proof.Fact) => sp.proof.sequentAndIntOfFact(f)._2)
            pretty("Subproof", topSteps*) +: prettyProofRecursive(sp.iProof, level + 1, currentTree, (if (i == 0) topMostIndices else IndexedSeq.empty) :+ i)
          case other =>
            val line = pretty(other.name)
            Seq(line)
        }
      }
    }

    val marker = "->"

    val lines = prettyProofRecursive(printedProof, 0, IndexedSeq.empty, IndexedSeq.empty)
    val maxStepNameLength = lines.map { case (_, _, stepName, _) => stepName.length }.maxOption.getOrElse(0)
    lines
      .map { case (isMarked, indices, stepName, sequent) =>
        val suffix = Seq(indices, rightPadSpaces(stepName, maxStepNameLength), sequent)
        val full = if (error.isDefined) (if (isMarked) marker else leftPadSpaces("", marker.length)) +: suffix else suffix
        full.mkString(" ")
      }
      ++ (error match {
        case None => Nil
        case Some((path, message)) => List(s"\nProof checker has reported an error at line ${path.mkString(".")}: $message")
      })
  }

  def prettyFullProofLines(printedProof: Library#Proof, error: Option[(IndexedSeq[Int], String)]): Seq[String] = {
    printedProof match {
      case proof: Library#Proof#InnerProof =>
        prettyFullProofLines(proof.parent, None) ++ prettyProofLines(proof, error).map("  " + _)
      case proof: Library#BaseProof =>
        prettyProofLines(proof, None)
    }
  }

  def prettyProof(proof: Library#Proof): String = prettyFullProofLines(proof, None).mkString("\n")
  def prettyProof(proof: Library#Proof, indent: Int): String = (" " * indent) + prettyFullProofLines(proof, None).mkString("\n" + (" " * indent))

  def prettyProof(proof: Library#Proof, error: Option[(IndexedSeq[Int], String)]): String = prettyFullProofLines(proof, error).mkString("\n")
  def prettyProof(proof: Library#Proof, indent: Int, error: Option[(IndexedSeq[Int], String)]): String = prettyFullProofLines(proof, None).mkString("\n" + " " * indent)

  def prettySimpleProof(proof: Library#Proof): String = prettyProofLines(proof, None).mkString("\n")
  def prettySimpleProof(proof: Library#Proof, indent: Int): String = (" " * indent) + prettyProofLines(proof, None).mkString("\n" + (" " * indent))

  def prettySimpleProof(proof: Library#Proof, error: Option[(IndexedSeq[Int], String)]): String = prettyProofLines(proof, error).mkString("\n")
  def prettySimpleProof(proof: Library#Proof, indent: Int, error: Option[(IndexedSeq[Int], String)]): String = prettyProofLines(proof, None).mkString("\n" + " " * indent)

  // def prettyProof(judgement: InvalidProofTactic): String = prettyProof(judgement.tactic.proof)

}
