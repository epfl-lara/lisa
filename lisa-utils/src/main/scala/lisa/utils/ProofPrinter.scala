package lisa.utils

import lisa.kernel.proof.SCProofCheckerJudgement
import lisa.utils.tactics.BasicStepTactic.SUBPROOF


//temporary - get merged wit regular printer in time
object ProofPrinter {

  private def spaceSeparator(compact: Boolean): String = if (compact) "" else " "

  private def commaSeparator(compact: Boolean, symbol: String = ","): String = s"$symbol${spaceSeparator(compact)}"


  def prettyProof(printedProof:Library#Proof, error: Option[(IndexedSeq[Int], String)]): String = {
    def computeMaxNumberingLengths(proof: Library#Proof, level: Int, result: IndexedSeq[Int]): IndexedSeq[Int] = {
      val resultWithCurrent = result.updated(
        level,
        (Seq((proof.getSteps.size - 1).toString.length, result(level)) ++ (if (proof.getImports.nonEmpty) Seq((-proof.getImports.size).toString.length) else Seq.empty)).max
      )
      proof.getSteps.collect { case ps: proof.ProofStep if ps.tactic.isInstanceOf[SUBPROOF] => ps.tactic.asInstanceOf[SUBPROOF]}
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
            Printer.prettySequent(imp._2)
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
            Printer.prettySequent(step.bot)
          )

        step.tactic match {
          case sp: SUBPROOF =>
            val topSteps : Seq[Int] = sp.premises.map((f:sp.proof.Fact) => sp.proof.sequentAndIntOfFact(f)._2)
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
      .mkString("\n") + (error match {
      case None => ""
      case Some((path, message)) => s"\nProof checker has reported an error at line ${path.mkString(".")}: $message"
    })
  }

  def prettyProof(proof: Library#Proof): String = prettyProof(proof, None)
  
  //def prettyProof(judgement: InvalidProofTactic): String = prettyProof(judgement.tactic.proof)

}
