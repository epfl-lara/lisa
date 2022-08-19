package lisa.front.printer

import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofCheckerJudgement.*
import lisa.kernel.proof.{SCProofCheckerJudgement, SequentCalculus as SC}
import lisa.kernel.fol.FOL
import lisa.kernel.proof.SequentCalculus.SCProofStep
import lisa.front.*
import lisa.front.parser.{FrontSymbols, KernelRuleIdentifiers}
import lisa.front.printer.FrontPositionedPrinter
import lisa.front.printer.FrontPrintStyle.{Ascii, Latex, Unicode}
import lisa.utils.ProofsShrink

object KernelPrinter {

  private case class ProofWrapper(steps: IndexedSeq[StepWrapper], imports: IndexedSeq[Sequent])
  private sealed abstract class StepWrapper {
    val name: String
    val sequent: Sequent
    val premises: Seq[Int]
    val parameters: Seq[String]
  }
  private case class NormalStepWrapper(name: String, premises: Seq[Int], sequent: Sequent, parameters: Seq[String]) extends StepWrapper
  private case class SubproofStepWrapper(name: String, proof: ProofWrapper, premises: Seq[Int]) extends StepWrapper {
    override val sequent: Sequent = proof.steps.last.sequent
    override val parameters: Seq[String] = Seq.empty
  }

  private def sequentFromKernel(s: lisa.kernel.proof.SequentCalculus.Sequent): Sequent = {
    def sorted(seq: IndexedSeq[Formula]): IndexedSeq[Formula] = seq.sortBy(_.toString)
    Sequent(sorted(s.left.toIndexedSeq.map(fromKernel)), sorted(s.right.toIndexedSeq.map(fromKernel)))
  }

  def prettyProof(scProof: SCProof, style: FrontPrintStyle = FrontPrintStyle.Unicode, compact: Boolean = false, explicit: Boolean = false): String =
    prettyJudgedProof(SCValidProof(scProof), style, compact, explicit)

  def prettyJudgedProof(judgement: SCProofCheckerJudgement, style: FrontPrintStyle = FrontPrintStyle.Unicode, compact: Boolean = false, explicit: Boolean = false): String = {
    val scProof = judgement.proof
    val p = FrontPrintParameters(style, compact)
    val r = KernelRuleIdentifiers(p.s)
    def prettyName(name: String): String = style match {
      case FrontPrintStyle.Latex => raw"\text{$name}"
      case _ => name
    }
    def prettyParameters(parameters: Seq[String]): String =
      if(parameters.isEmpty) "" else s"${p.s.SquareBracketOpen}${parameters.mkString(p.s.Semicolon + (if(compact) "" else " "))}${p.s.SquareBracketClose}"
    def prettyFormula(f: FOL.Formula): String = FrontPositionedPrinter.prettyFormula(fromKernel(f), style, compact)
    def prettyTerm(t: FOL.Term): String = FrontPositionedPrinter.prettyTerm(fromKernel(t), style, compact)
    def prettyFunction(label: FOL.TermLabel, lambda: FOL.LambdaTermTerm): String =
      prettyFormula(FOL.PredicateFormula(FOL.equality, Seq(FOL.Term(label, lambda.vars.map(FOL.VariableTerm)), lambda.body)))
    def prettyPredicate(label: FOL.PredicateLabel, lambda: FOL.LambdaTermFormula): String =
      prettyFormula(FOL.ConnectorFormula(FOL.Iff, Seq(FOL.PredicateFormula(label, lambda.vars.map(FOL.VariableTerm)), lambda.body)))
    val placeholder = "_"

    def wrap(scProof: lisa.kernel.proof.SCProof): ProofWrapper = {
      val steps = scProof.steps.map { step =>
        val name = r.identify(step)
        val parameters: Seq[String] = step match {
          case s: SC.Hypothesis => Seq(prettyFormula(s.phi))
          case s: SC.Cut => Seq(prettyFormula(s.phi))
          case _: SC.Rewrite => Seq.empty
          case _: SC.Weakening => Seq.empty
          case s: SC.LeftAnd => Seq(s.phi, s.psi).map(prettyFormula)
          case s: SC.RightAnd => s.cunjuncts.map(prettyFormula)
          case s: SC.LeftOr => s.disjuncts.map(prettyFormula)
          case s: SC.RightOr => Seq(s.phi, s.psi).map(prettyFormula)
          case s: SC.LeftImplies => Seq(s.phi, s.psi).map(prettyFormula)
          case s: SC.RightImplies => Seq(s.phi, s.psi).map(prettyFormula)
          case s: SC.LeftIff => Seq(s.phi, s.psi).map(prettyFormula)
          case s: SC.RightIff => Seq(s.phi, s.psi).map(prettyFormula)
          case s: SC.LeftNot => Seq(prettyFormula(s.phi))
          case s: SC.RightNot => Seq(prettyFormula(s.phi))
          case s: SC.LeftForall => Seq(prettyFormula(s.phi), s.x.id, prettyTerm(s.t))
          case s: SC.RightForall => Seq(prettyFormula(s.phi), s.x.id)
          case s: SC.LeftExists => Seq(prettyFormula(s.phi), s.x.id)
          case s: SC.RightExists => Seq(prettyFormula(s.phi), s.x.id, prettyTerm(s.t))
          case s: SC.LeftExistsOne => Seq(prettyFormula(s.phi), s.x.id)
          case s: SC.RightExistsOne => Seq(prettyFormula(s.phi), s.x.id)
          case s: SC.LeftRefl => Seq(prettyFormula(s.fa))
          case s: SC.RightRefl => Seq(prettyFormula(s.fa))
          case s: SC.LeftSubstEq => s.equals.flatMap { case (l, r) => Seq(l, r) }.map(prettyTerm)
            :+ prettyPredicate(FOL.ConstantPredicateLabel(placeholder, s.lambdaPhi.vars.size), s.lambdaPhi)
          case s: SC.RightSubstEq => s.equals.flatMap { case (l, r) => Seq(l, r) }.map(prettyTerm)
            :+ prettyPredicate(FOL.ConstantPredicateLabel(placeholder, s.lambdaPhi.vars.size), s.lambdaPhi)
          case s: SC.LeftSubstIff => s.equals.flatMap { case (l, r) => Seq(l, r) }.map(prettyFormula)
            :+ prettyPredicate(
              FOL.ConstantPredicateLabel(placeholder, s.lambdaPhi.vars.size),
              FOL.LambdaTermFormula(s.lambdaPhi.vars.map(v => FOL.VariableLabel(v.id)), s.lambdaPhi.body)
            )
          case s: SC.RightSubstIff => s.equals.flatMap { case (l, r) => Seq(l, r) }.map(prettyFormula)
            :+ prettyPredicate(
            FOL.ConstantPredicateLabel(placeholder, s.lambdaPhi.vars.size),
            FOL.LambdaTermFormula(s.lambdaPhi.vars.map(v => FOL.VariableLabel(v.id)), s.lambdaPhi.body)
          )
          case s: SC.InstFunSchema => s.insts.toSeq.map { case (label, lambda) =>
            label match {
              case l: FOL.SchematicTermLabel => prettyFunction(l, lambda)
            }
          }
          case s: SC.InstPredSchema => s.insts.toSeq.map { case (label, lambda) => prettyPredicate(label, lambda) }
          case SC.SCSubproof(_, _, true) => Seq.empty
          case SC.SCSubproof(_, _, false) => Seq.empty
        }
        step match {
          case SC.SCSubproof(sp, premises, true) =>
            SubproofStepWrapper(name, wrap(sp), premises)
          case _ =>
            NormalStepWrapper(name, step.premises, sequentFromKernel(step.bot), if(explicit) parameters else Seq.empty)
        }
      }

      ProofWrapper(steps, scProof.imports.map(sequentFromKernel))
    }

    val proof = wrap(scProof)

    def prettyStepName(step: StepWrapper): String =
      Seq(
        step.name,
        if(style == Latex) "~" else " ",
        step.premises.map(i => if(style == Latex && i < 0) s"{$i}" else i).mkString(", "),
      ).mkString

    val columnInterleaving = style match {
      case Latex => " & "
      case _ => " "
    }

    def computeNumberColumnEnds(proof: ProofWrapper, nextColumnStart: Int, path: Seq[Int]): Map[Seq[Int], Int] = {
      val maxCharCount = Seq(-proof.imports.size, proof.steps.size - 1).map(_.toString.length).max
      val columnEnd = nextColumnStart + maxCharCount - 1
      val newNextColumnStart = columnEnd + 1 + columnInterleaving.length
      proof.steps.zipWithIndex.map {
        case (SubproofStepWrapper(_, subProof, _), i) =>
          computeNumberColumnEnds(subProof, newNextColumnStart, i +: path)
        case _ => Map.empty
      }.fold(Map.empty)(_ ++ _) + (path -> columnEnd)
    }
    val numberColumnEnds = computeNumberColumnEnds(proof, 0, Seq.empty)
    val maximumNumberColumnEnd = numberColumnEnds.values.max
    val maximumNumberColumnDepth = numberColumnEnds.keys.map(_.size).max

    def computeMaximumRuleNameLength(proof: ProofWrapper): Int =
      proof.steps.map {
        case step @ SubproofStepWrapper(_, proof, _) => Math.max(prettyStepName(step).length, computeMaximumRuleNameLength(proof))
        case other => prettyStepName(other).length
      }.max
    val maximumRuleNameLength = computeMaximumRuleNameLength(proof)

    val proofStepIndicator = s"${p.s.Implies} "
    val proofStepNoIndicator = " " * proofStepIndicator.length

    def recursivePrint(proof: ProofWrapper, path: Seq[Int]): Seq[(String, String)] = {
      val importsPairs = proof.imports.zipWithIndex.map { case (s, i) => (-(i + 1), NormalStepWrapper(prettyName("Import"), Seq.empty, s, Seq.empty)) }.reverse
      val stepsTriplets = proof.steps.zipWithIndex.map { case (step, i) =>
        val option = step match {
          case SubproofStepWrapper(_, proof, _) => Some(proof)
          case _ => None
        }
        ((i, step), option)
      }

      def prettyLine(i: Int, step: StepWrapper): String = {
        val numberColumn = i.toString
        val numberColumnEnd = numberColumnEnds(path)
        val nameWithPremises = prettyStepName(step)

        val (leftLength, rightLength) = (numberColumnEnd - numberColumn.length + 1, maximumNumberColumnEnd - numberColumnEnd)
        val (leftSpace, rightSpace) = (columnInterleaving * path.size, columnInterleaving * (maximumNumberColumnDepth - path.size))

        val fullPath = i +: path

        val prefix = judgement match {
          case SCValidProof(_) => ""
          case SCInvalidProof(_, errorPath, _) => if(errorPath.reverse == fullPath) proofStepIndicator else proofStepNoIndicator
        }

        prefix +
          leftSpace + (" " * (leftLength - leftSpace.length)) +
          numberColumn +
          (" " * (rightLength - rightSpace.length)) + rightSpace +
          columnInterleaving +
          nameWithPremises +
          (" " * (maximumRuleNameLength - nameWithPremises.length)) +
          columnInterleaving +
          FrontPositionedPrinter.prettySequent(step.sequent, style, compact)
      }

      importsPairs.map(prettyLine).map(_ -> "") ++ stepsTriplets.flatMap { case ((i, step), option) =>
        (prettyLine(i, step), prettyParameters(step.parameters)) +: option.toSeq.flatMap(proof => recursivePrint(proof, i +: path))
      }
    }

    val lineSeparator = style match {
      case Latex => " \\\\\n"
      case _ => "\n"
    }

    val errorSeq = judgement match {
      case SCValidProof(_) => Seq.empty
      case SCInvalidProof(_, path, message) => Seq(s"Proof checker has reported an error at line ${path.mkString(".")}: $message")
    }

    val allLinesPairs = recursivePrint(proof, Seq.empty)
    val maximumLengthFirst = allLinesPairs.map { case (first, _) => first.length }.max
    val contentProof = allLinesPairs.map { case (first, second) =>
      Seq(first, " " * (maximumLengthFirst - first.length), if(explicit) columnInterleaving else "", second).mkString.replaceAll("\\s+$", "")
    }
    val content = (contentProof ++ errorSeq).mkString(lineSeparator)

    style match {
      case FrontPrintStyle.Latex =>
        Seq(
          raw"\tiny",
          raw"$$\begin{array}{${(0 to maximumNumberColumnDepth).map(i => raw"r${if(i < maximumNumberColumnDepth) raw"@{\hskip 0.1cm}" else ""}").mkString}ll${if(explicit) "l" else ""}}",
          content,
          raw"\end{array}$$",
          raw"\normalsize",
        ).mkString("\n")
      case _ => content
    }
  }

  def prettyProofTreeLatex(scProof: lisa.kernel.proof.SCProof): String = {
    val r = KernelRuleIdentifiers(FrontSymbols.FrontLatexSymbols)
    val flatProof = ProofsShrink.flattenProof(scProof)
    def postOrder(step: SCProofStep): Seq[Either[SCProofStep, SC.Sequent]] =
      step.premises.flatMap { i =>
        if(i >= 0) postOrder(flatProof.steps(i)) else Seq(Right(flatProof.imports(-(i + 1))))
      } :+ Left(step)
    val orderedSteps = postOrder(flatProof.steps.last)
    val orderedStepsOptionals: Seq[Either[SCProofStep, Option[SC.Sequent]]] = orderedSteps.flatMap {
      case Left(step) => (if(step.premises.isEmpty) Seq(Right(None)) else Seq.empty) ++ Seq(Left(step))
      case Right(sequent) => Seq(Right(Some(sequent)))
    }

    def prettySequent(sequent: SC.Sequent): String =
      FrontPositionedPrinter.prettySequent(sequentFromKernel(sequent), Latex)

    (raw"\begin{prooftree}" +:
      orderedStepsOptionals.map {
        case Left(step) => raw"\infer${Math.max(step.premises.size, 1)}[$$${r.identify(step)}$$]{${prettySequent(step.bot)}}"
        case Right(None) => raw"\hypo{}"
        case Right(Some(sequent)) => raw"\hypo{${prettySequent(sequent)}}"
      } :+
      raw"\end{prooftree}").mkString("\n")
  }

}
