package lisa.front.parser

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.proof.SCProof
import lisa.front.parser.FrontParsed.*
import lisa.front.parser.FrontReadingException.ResolutionException
import lisa.front.parser.FrontResolver.*

import scala.util.{Failure, Success, Try}
import scala.util.parsing.input.Position

private[parser] object KernelResolver {

  private def tryResolve[T](t: => T): Option[T] = Try(t) match {
    case Success(value) => Some(value)
    case Failure(exception) => exception match {
      case _: ResolutionException => None
      case _ => throw new Exception(exception)
    }
  }
  private def all[T](t: => Seq[Option[T]]): Option[Seq[T]] = if(t.forall(_.nonEmpty)) Some(t.flatten) else None

  private object Formula {
    def unapply(tree: ParsedTopTermOrFormula): Option[Formula] = tryResolve(resolveFormula(tree))
  }
  private object FormulaSeq {
    def unapplySeq(trees: Seq[ParsedTopTermOrFormula]): Option[Seq[Formula]] = all(trees.map(tree => tryResolve(resolveFormula(tree))))
  }
  private object Term {
    def unapply(tree: ParsedTopTermOrFormula): Option[Term] = tryResolve(resolveTerm(tree))
  }
  private object TermSeq {
    def unapplySeq(trees: Seq[ParsedTopTermOrFormula]): Option[Seq[Term]] = all(trees.map(tree => tryResolve(resolveTerm(tree))))
  }
  private object Identifier {
    def unapply(tree: ParsedTopTermOrFormula): Option[String] = tree.termOrFormula match {
      case ParsedConstant(identifier) => Some(identifier)
      case _ => None
    }
  }

  private object FunctionMap {
    def unapplySeq(trees: Seq[ParsedTopTermOrFormula]): Option[Seq[(SchematicTermLabel, LambdaTermTerm)]] = {
      all(trees.map {
        case ParsedTopTermOrFormula(freeVariables, ParsedEqual(left, term)) =>
          val opt = left match {
            case ParsedSchema(identifier, false) => Some((identifier, Seq.empty))
            case ParsedApplication(ParsedSchema(identifier, false), args) => Some((identifier, args))
            case _ => None
          }
          opt.flatMap { case (identifier, args) =>
            all(args.map {
              case ParsedSchema(arg, false) => Some(VariableLabel(arg))
              case _ => None
            }).flatMap(arguments =>
              Term.unapply(ParsedTopTermOrFormula(freeVariables, term))
                .map(body => SchematicFunctionLabel(identifier, args.size) -> LambdaTermTerm(arguments, body))
            )
          }
        case _ => None
      })
    }
  }
  private object PredicateMap {
    def unapplySeq(trees: Seq[ParsedTopTermOrFormula]): Option[Seq[(SchematicVarOrPredLabel, LambdaTermFormula)]] = {
      all(trees.map {
        case ParsedTopTermOrFormula(freeVariables, ParsedIff(left, term)) =>
          val opt = left match {
            case ParsedSchema(identifier, true) => Some((identifier, Seq.empty))
            case ParsedApplication(ParsedSchema(identifier, true), args) => Some((identifier, args))
            case _ => None
          }
          opt.flatMap { case (identifier, args) =>
            all(args.map {
              case ParsedSchema(arg, false) => Some(VariableLabel(arg))
              case _ => None
            }).flatMap(arguments =>
              Formula.unapply(ParsedTopTermOrFormula(freeVariables, term))
                .map(body => SchematicPredicateLabel(identifier, args.size) -> LambdaTermFormula(arguments, body))
            )
          }
        case _ => None
      })
    }
  }

  private def resolveProofStep(tree: ParsedProofStep, kernelRuleIdentifiers: KernelRuleIdentifiers): SCProofStep = {
    val R = kernelRuleIdentifiers
    require(!Seq(R.Import, R.SubproofShown, R.SubproofHidden).contains(tree.ruleName))

    val placeholder = "_"
    def throwInvalidStep(): Nothing =
      throw ResolutionException(s"Incorrect premises and/or arguments for step '${tree.ruleName}'", tree.stepPosition)

    val bot = resolveSequent(tree.conclusion)
    (tree.ruleName, tree.premises, tree.parameters) match {
      case (R.Hypothesis, Seq(), Seq(Formula(phi))) => Hypothesis(bot, phi)
      case (R.Cut, Seq(t1, t2), Seq(Formula(phi))) => Cut(bot, t1, t2, phi)
      case (R.Rewrite, Seq(t1), Seq()) => Rewrite(bot, t1)
      case (R.Weakening, Seq(t1), Seq()) => Weakening(bot, t1)
      case (R.LeftAnd, Seq(t1), Seq(Formula(phi), Formula(psi))) => LeftAnd(bot, t1, phi, psi)
      case (R.RightAnd, premises, FormulaSeq(conjuncts*)) if conjuncts.size == premises.size => RightAnd(bot, premises, conjuncts)
      case (R.LeftOr, premises, FormulaSeq(conjuncts*)) if conjuncts.size == premises.size => LeftOr(bot, premises, conjuncts)
      case (R.RightOr, Seq(t1), Seq(Formula(phi), Formula(psi))) => RightOr(bot, t1, phi, psi)
      case (R.LeftImplies, Seq(t1, t2), Seq(Formula(phi), Formula(psi))) => LeftImplies(bot, t1, t2, phi, psi)
      case (R.RightImplies, Seq(t1), Seq(Formula(phi), Formula(psi))) => RightImplies(bot, t1, phi, psi)
      case (R.LeftIff, Seq(t1), Seq(Formula(phi), Formula(psi))) => LeftIff(bot, t1, phi, psi)
      case (R.RightIff, Seq(t1, t2), Seq(Formula(phi), Formula(psi))) => RightIff(bot, t1, t2, phi, psi)
      case (R.LeftNot, Seq(t1), Seq(Formula(phi))) => LeftNot(bot, t1, phi)
      case (R.RightNot, Seq(t1), Seq(Formula(phi))) => RightNot(bot, t1, phi)
      case (R.LeftForall, Seq(t1), Seq(Formula(phi), Identifier(x), Term(t))) => LeftForall(bot, t1, phi, VariableLabel(x), t)
      case (R.RightForall, Seq(t1), Seq(Formula(phi), Identifier(x))) => RightForall(bot, t1, phi, VariableLabel(x))
      case (R.LeftExists, Seq(t1), Seq(Formula(phi), Identifier(x))) => LeftExists(bot, t1, phi, VariableLabel(x))
      case (R.RightExists, Seq(t1), Seq(Formula(phi), Identifier(x), Term(t))) => RightExists(bot, t1, phi, VariableLabel(x), t)
      case (R.LeftExistsOne, Seq(t1), Seq(Formula(phi), Identifier(x))) => LeftExistsOne(bot, t1, phi, VariableLabel(x))
      case (R.RightExistsOne, Seq(t1), Seq(Formula(phi), Identifier(x))) => RightExistsOne(bot, t1, phi, VariableLabel(x))
      case (R.LeftRefl, Seq(t1), Seq(Formula(fa))) => LeftRefl(bot, t1, fa)
      case (R.RightRefl, Seq(), Seq(Formula(fa))) => RightRefl(bot, fa)
      case (R.LeftSubstEq, Seq(t1), parameters) if parameters.size % 2 == 1 =>
        (parameters.init, parameters.last) match {
          case (TermSeq(terms*), Formula(ConnectorFormula(Iff, Seq(PredicateFormula(ConstantPredicateLabel(`placeholder`, _), args), body)))) =>
            all(args.map {
              case VariableTerm(label) => Some(label)
              case _ => None
            }) match {
              case Some(vars) => LeftSubstEq(bot, t1, terms.grouped(2).collect { case Seq(a, b) => (a, b) }.toList, LambdaTermFormula(vars, body))
              case None => throwInvalidStep()
            }
          case _ => throwInvalidStep()
        }
      case (R.RightSubstEq, Seq(t1), parameters) if parameters.size % 2 == 1 =>
        (parameters.init, parameters.last) match {
          case (TermSeq(terms*), Formula(ConnectorFormula(Iff, Seq(PredicateFormula(ConstantPredicateLabel(`placeholder`, _), args), body)))) =>
            all(args.map {
              case VariableTerm(label) => Some(label)
              case _ => None
            }) match {
              case Some(vars) => RightSubstEq(bot, t1, terms.grouped(2).collect { case Seq(a, b) => (a, b) }.toList, LambdaTermFormula(vars, body))
              case None => throwInvalidStep()
            }
          case _ => throwInvalidStep()
        }
      case (R.LeftSubstIff, Seq(t1), parameters) if parameters.size % 2 == 1 =>
        (parameters.init, parameters.last) match {
          case (FormulaSeq(formulas*), Formula(ConnectorFormula(Iff, Seq(PredicateFormula(ConstantPredicateLabel(`placeholder`, _), args), body)))) =>
            all(args.map {
              case VariableTerm(label) => Some(VariableFormulaLabel(label.id))
              case _ => None
            }) match {
              case Some(vars) => LeftSubstIff(bot, t1, formulas.grouped(2).collect { case Seq(a, b) => (a, b) }.toList, LambdaFormulaFormula(vars, body))
              case None => throwInvalidStep()
            }
          case _ => throwInvalidStep()
        }
      case (R.RightSubstIff, Seq(t1), parameters) if parameters.size % 2 == 1 =>
        (parameters.init, parameters.last) match {
          case (FormulaSeq(formulas*), Formula(ConnectorFormula(Iff, Seq(PredicateFormula(ConstantPredicateLabel(`placeholder`, _), args), body)))) =>
            all(args.map {
              case VariableTerm(label) => Some(VariableFormulaLabel(label.id))
              case _ => None
            }) match {
              case Some(vars) => RightSubstIff(bot, t1, formulas.grouped(2).collect { case Seq(a, b) => (a, b) }.toList, LambdaFormulaFormula(vars, body))
              case None => throwInvalidStep()
            }
          case _ => throwInvalidStep()
        }
      case (R.FunInstantiation, Seq(t1), FunctionMap(map*)) => InstFunSchema(bot, t1, map.toMap)
      case (R.PredInstantiation, Seq(t1), PredicateMap(map*)) => InstPredSchema(bot, t1, map.toMap)
      case _ => throwInvalidStep()
    }
  }

  def resolveProof(tree: ParsedProof, symbols: FrontSymbols): SCProof = {
    val R = KernelRuleIdentifiers(symbols)

    case class StackEntry(steps: IndexedSeq[SCProofStep], imports: IndexedSeq[Sequent], subproofPremises: Seq[Int], nextLineNumber: Int, indentation: Int)

    def foldSubproofs(stack: Seq[StackEntry], position: Position): Option[SCSubproof] = {
      stack.foldLeft(None: Option[SCSubproof]) { (subproofOpt, entry) =>
        val premises = entry.subproofPremises
        val newSteps = subproofOpt match {
          case Some(proof) => entry.steps :+ proof.copy(premises = premises)
          case None => entry.steps
        }
        if(newSteps.isEmpty) {
          throw ResolutionException("This proof or subproof is incomplete", position)
        }
        Some(SCSubproof(SCProof(newSteps, entry.imports)))
      }
    }

    val (finalStack, finalExpectedDeeperIndentation) = tree.steps.foldLeft(
      (Seq.empty[StackEntry], true)
    ) { case ((stack, expectedDeeperIndentation), parsedStep) =>
      // The true indentation of the current step
      val rightIndentation = parsedStep.indentation + parsedStep.line.toString.length

      val newStack =
        if(expectedDeeperIndentation) { // Either the first line of a subproof or the first line of the proof
          stack match {
            case entry +: _ => // First step inside a subproof
              if (rightIndentation <= entry.indentation) {
                throw ResolutionException("The content of this subproof must be indented further", parsedStep.stepPosition)
              }
              val importsSize = entry.subproofPremises.size
              if(-parsedStep.line != importsSize) {
                throw ResolutionException(s"The parent subproof declared $importsSize premise(s), therefore this line must start with index ${-importsSize}", parsedStep.stepPosition)
              }
            case _ => // Very first line of the proof
              ()
          }
          if (parsedStep.line > 0) {
            throw ResolutionException(s"The index of the first proof step cannot be strictly positive", parsedStep.stepPosition)
          }
          val entry = StackEntry(IndexedSeq.empty, IndexedSeq.empty, Seq.empty, parsedStep.line, rightIndentation)
          entry +: stack
        } else { // A line at the same level or lower
          assert(stack.nonEmpty) // Invariant

          val indentationIndex = stack.zipWithIndex.find { case (entry, _) => entry.indentation == rightIndentation }.map(_._2)
          indentationIndex match {
            case Some(delta) =>
              val previousEntry: StackEntry = stack(delta)
              previousEntry.copy(steps = previousEntry.steps ++ foldSubproofs(stack.take(delta), parsedStep.stepPosition).map(sp => sp.copy(premises = previousEntry.subproofPremises)).toSeq) +: stack.drop(delta + 1)
            case None =>
              throw ResolutionException("This step is not properly indented", parsedStep.stepPosition)
          }
        }

      assert(newStack.nonEmpty) // Invariant

      val entry = newStack.head
      val tail = newStack.tail

      if (parsedStep.line != entry.nextLineNumber) {
        throw ResolutionException(s"Expected line to be numbered ${entry.nextLineNumber}, but got ${parsedStep.line} instead", parsedStep.stepPosition)
      }

      val isImport = parsedStep.ruleName == R.Import
      val isSubproof = parsedStep.ruleName == R.SubproofShown // Hidden is excluded from this

      if(parsedStep.ruleName == R.SubproofHidden) {
        throw ResolutionException("Cannot parse a hidden subproof", parsedStep.stepPosition)
      }

      if(parsedStep.line < 0) {
        if(!isImport) {
          throw ResolutionException("Negative step indices must necessarily be import statements", parsedStep.stepPosition)
        }
      } else {
        if(isImport) {
          throw ResolutionException("Import statements can only appear on negative indices steps", parsedStep.stepPosition)
        }
      }

      if(isImport && parsedStep.premises.nonEmpty) {
        throw ResolutionException("Import statements cannot have premises", parsedStep.stepPosition)
      }

      if(!isImport) {
        parsedStep.premises.foreach { premise =>
          if((premise < 0 && -premise > entry.imports.size) || (premise >= 0 && premise >= entry.steps.size)) {
            throw ResolutionException(s"Premise $premise is out of bounds", parsedStep.stepPosition)
          }
        }
      }

      val sequent = resolveSequent(parsedStep.conclusion)

      val newEntry = entry.copy(nextLineNumber = entry.nextLineNumber + 1, subproofPremises = Seq.empty)

      if(isImport) {
        (newEntry.copy(imports = sequent +: newEntry.imports) +: tail, false)
      } else if(isSubproof) {
        (newEntry.copy(subproofPremises = parsedStep.premises) +: tail, true)
      } else {
        val newStep = resolveProofStep(parsedStep, R)
        (newEntry.copy(steps = newEntry.steps :+ newStep) +: tail, isSubproof) // FIXME spurious `isSubproof` (variable is always false here)
      }
    }

    val lastPosition = tree.steps.last.stepPosition
    if(finalExpectedDeeperIndentation) {
      throw ResolutionException("Empty trailing subproof", lastPosition)
    }

    val finalStep = foldSubproofs(finalStack, lastPosition)
    finalStep.get.sp
  }

}
