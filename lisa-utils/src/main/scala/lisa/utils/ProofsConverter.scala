package lisa.utils

import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.K
import lisa.utils.KernelHelpers.lambda
import lisa.prooflib.ProofTacticLib.*
import lisa.fol.FOL as F
import lisa.fol.FOLHelpers.*

object ProofsConverter {

// TODO: remove unnecessary variables "val s_..." in generated proofs -> need to detect which steps are used later in other steps
// TODO: generate more realistic variable names

  private def indent(s: String, indent: Int = 2): String = s.split("\n").map(s => if s == "" then "" else " " * indent + s).mkString("\n")
  private def unindent(s: String, indent: Int = 2): String = s.split("\n").map(_.stripPrefix(" " * indent)).mkString("\n")

  /**
   * Converts a Sequent, Formula or Term to a valid Scala/Lisa code
   *
   * @param f formula to convert
   * @return Scala code representing the formula in string format
   */
  private def any2code(a: K.Sequent | K.Formula | K.Term): String = (a match
    case sq: K.Sequent => asFront(sq)
    case form: K.Formula => asFront(form)
    case term: K.Term => asFront(term)
  ).toString.replace("⇒", "==>").replace("⇔", "<=>")

  /**
   * Converts a SCProof to a valid Scala/Lisa code using tactics.
   *
   * @param p proof to convert
   * @return Scala code representing the proof in string format
   */
  private def scproof2code(p: K.SCProof): String = {
    def scproof2codeAux(p: K.SCProof, varPrefix: String = "s", implicitPremises: Seq[String] = Seq.empty): String = {
      def scproofstep2code(ps: SCProofStep, stepNum: Int, implicitPremises: Seq[String], varPrefix: String): String = {

        def index2stepvar(i: Int): String =
          if i < -implicitPremises.size then throw new Exception(s"step $i is not defined")
          else if i < 0 then implicitPremises(-i - 1)
          else s"${varPrefix}_$i"

        ps match
          case Sorry(_) => "sorry"
          case sp @ SCSubproof(_, _) =>
            indent(
              s"val ${varPrefix}_$stepNum = have(${any2code(sp.bot)}) subproof {\n" +
                scproof2codeAux(sp.sp, s"${varPrefix}_$stepNum", sp.premises.map(index2stepvar)) +
                "\n}"
            )
          case _ =>
            var tacticName = ps.getClass.getSimpleName
            var opening = "("
            var closing = ")"
            ps match
              case Restate(_, _) => opening = ".from("
              case RestateTrue(_) => tacticName = "Restate"
              case LeftSubstEq(_, _, equals, lambdaPhi) =>
                tacticName = s"LeftSubstEq.withParametersSimple(List(${equals
                    .map((a, b) => s"((${any2code(a.body)}), (${any2code(b.body)}))")
                    .mkString(", ")}), lambda(Seq(${lambdaPhi._1.map(asFrontLabel).mkString(", ")}), ${any2code(lambdaPhi._2)}))"
              case RightSubstEq(_, _, equals, lambdaPhi) =>
                tacticName = s"RightSubstEq.withParametersSimple(List(${equals
                    .map((a, b) => s"((${any2code(a.body)}), (${any2code(b.body)}))")
                    .mkString(", ")}), lambda(Seq(${lambdaPhi._1.map(asFrontLabel).mkString(", ")}), ${any2code(lambdaPhi._2)}))"
              case LeftSubstIff(_, _, equals, lambdaPhi) =>
                tacticName = s"LeftSubstIff.withParametersSimple(List(${equals
                    .map((a, b) => s"((${any2code(a.body)}), (${any2code(b.body)}))")
                    .mkString(", ")}), lambda(Seq(${lambdaPhi._1.map(asFrontLabel).mkString(", ")}), ${any2code(lambdaPhi._2)}))"
              case RightSubstIff(_, _, equals, lambdaPhi) =>
                tacticName = s"RightSubstIff.withParametersSimple(List(${equals
                    .map((a, b) => s"((${any2code(a.body)}), (${any2code(b.body)}))")
                    .mkString(", ")}), lambda(Seq(${lambdaPhi._1.map(asFrontLabel).mkString(", ")}), ${any2code(lambdaPhi._2)}))"
              case InstSchema(_, _, mCon, mPred, mTerm) =>
                if mCon.isEmpty && mPred.isEmpty then
                  tacticName = s"InstFunSchema(Map(${mTerm.toList
                      .map((k, v) => s"${asFrontLabel(k)} -> ${any2code(v.body)}")
                      .mkString(", ")}))"
                else if mCon.isEmpty && mTerm.isEmpty then
                  tacticName = s"InstPredSchema(Map(${mPred.toList
                      .map((k, v) => s"${asFrontLabel(k)} -> ${any2code(v.body)}")
                      .mkString(", ")}))"
                else throw new Exception("InstSchema not implemented")
              case _ => ()

            indent(
              s"val ${varPrefix}_$stepNum = " + (
                if (ps.premises.size == 1 && ps.premises.head + 1 == stepNum && stepNum > 0)
                then s"thenHave(${any2code(ps.bot)}) by $tacticName"
                else
                  s"have(${any2code(ps.bot)}) by $tacticName" + (
                    if ps.premises.size == 0 then ""
                    else s"$opening${ps.premises.map(index2stepvar).mkString(", ")}$closing"
                  )
              )
            )
      }

      p.steps.zipWithIndex.map((ps, i) => scproofstep2code(ps, i, implicitPremises, varPrefix)).mkString("\n")
    }
    unindent(scproof2codeAux(p))
  }

  /**
   * Extracts all formulas from a proof
   *
   * @param proof proof to extract formulas from
   * @return set of formulas
   */
  private def extractFormulasFromProof(proof: K.SCProof): Set[K.Formula] =
    proof.steps.foldLeft(Set.empty[K.Formula])((prev, next) => {
      prev ++ (next match
        case sp @ SCSubproof(subproof, _) => extractFormulasFromProof(subproof)
        case LeftSubstEq(_, _, _, lambdaPhi) => Seq(lambdaPhi._2, K.sequentToFormula(next.bot))
        case RightSubstEq(_, _, _, lambdaPhi) => Seq(lambdaPhi._2, K.sequentToFormula(next.bot))
        case LeftSubstIff(_, _, _, lambdaPhi) => Seq(lambdaPhi._2, K.sequentToFormula(next.bot))
        case RightSubstIff(_, _, _, lambdaPhi) => Seq(lambdaPhi._2, K.sequentToFormula(next.bot))
        case _ => Seq(K.sequentToFormula(next.bot))
      )
    })

  /**
   * Extracts all variables, functions, formula variables, predicates and connectors from a set of formulas
   *
   * @param formulas set of formulas to extract variables from
   * @return tuple of sets of variables, functions, formula variables, predicates and connectors
   */
  private def extractVariables(
      formulas: Set[K.Formula]
  ): (Set[K.VariableLabel], Set[K.SchematicFunctionLabel], Set[K.VariableFormulaLabel], Set[K.SchematicPredicateLabel], Set[K.SchematicConnectorLabel]) =
    def extractVariablesAux(
        formula: K.Formula
    ): (Set[K.VariableLabel], Set[K.SchematicFunctionLabel], Set[K.VariableFormulaLabel], Set[K.SchematicPredicateLabel], Set[K.SchematicConnectorLabel]) =
      var variableSet = formula.schematicTermLabels.collect { case v: K.VariableLabel => v }
      var functionSet = formula.schematicTermLabels.collect { case f: K.SchematicFunctionLabel => f }
      var formulaVariableSet = formula.schematicAtomicLabels.collect { case v: K.VariableFormulaLabel => v }
      var predicateSet = formula.schematicAtomicLabels.collect { case p: K.SchematicPredicateLabel => p }
      var connectorSet = formula.schematicConnectorLabels.collect { case c: K.SchematicConnectorLabel => c }
      (variableSet, functionSet, formulaVariableSet, predicateSet, connectorSet)

    formulas.foldLeft(
      (Set.empty[K.VariableLabel], Set.empty[K.SchematicFunctionLabel], Set.empty[K.VariableFormulaLabel], Set.empty[K.SchematicPredicateLabel], Set.empty[K.SchematicConnectorLabel])
    )((prev, next) => {
      val (variableSet, functionSet, formulaVariableSet, predicateSet, connectorSet) = prev
      val (variableSet_, functionSet_, formulaVariableSet_, predicateSet_, connectorSet_) = extractVariablesAux(next)
      (
        variableSet ++ variableSet_,
        functionSet ++ functionSet_,
        formulaVariableSet ++ formulaVariableSet_,
        predicateSet ++ predicateSet_,
        connectorSet ++ connectorSet_
      )
    })

  /**
   * Generates a valid Scala/Lisa code to declare variables, functions, formula variables, predicates and connectors
   * used in a set of formulas
   *
   * @param formulas set of formulas to generate variables for
   * @param accessibility accessibility of the variables (e.g. "private")
   *
   * @return Scala code representing the variables in string format
   */
  private def generateVariablesCode(formulas: Set[K.Formula], accessibility: String): String =
    val (variableSet, functionSet, formulaVariableSet, predicateSet, connectorSet) = extractVariables(formulas)
    val access = if accessibility != "" then accessibility.strip() + " " else ""
    (variableSet.map(v => access + s"val ${v.id} = variable").toList.sorted ++
      functionSet.map(f => access + s"val ${f.id} = function[${f.arity}]").toList.sorted ++
      formulaVariableSet.map(v => access + s"val ${v.id} = formulaVariable").toList.sorted ++
      predicateSet.map(p => access + s"val ${p.id} = predicate[${p.arity}]").toList.sorted ++
      connectorSet.map(c => access + s"val ${c.id} = connector[${c.arity}]").toList.sorted).mkString("\n")

  /**
   * Generates a valid Scala/Lisa code to declare variables, functions, formula variables, predicates and connectors
   * used in a proof
   *
   * @param proof proof to generate variables for
   * @param accessibility accessibility of the variables (e.g. "private")
   *
   * @return Scala code representing the variables in string format
   */
  private def generateVariablesCode(proof: K.SCProof, accessibility: String = "private"): String =
    generateVariablesCode(extractFormulasFromProof(proof), accessibility)

  /**
   * Generates a valid Scala/Lisa code of a theorem and its proof
   *
   * @param name name of the theorem
   * @param proof proof of the theorem
   *
   * @return Scala code representing the theorem in string format
   */
  private def generateTheoremCode(name: String, proof: K.SCProof): String = {
    s"val $name = Theorem(\n" +
      indent(any2code(proof.conclusion)) +
      s"\n) {\n" +
      indent(scproof2code(proof)) +
      s"\n}"
  }

  /**
   * Generates a valid Scala/Lisa code of a theorem and its proof in a standalone file, including the necessary variables declarations.
   * The theorem and its proof must be self-contained, i.e. no dependencies to other theorems, axioms, definitions, etc.
   *
   * @param name name of the theorem
   * @param proof proof of the theorem
   *
   * @return Scala code representing the theorem in string format
   */
  def generateStandaloneTheoremFileContent(name: String, proof: K.SCProof): String =
    val camelName = "[A-Za-z0-9]+".r.findAllIn(name).map(_.capitalize).mkString
    s"object $camelName extends lisa.Main {\n\n" +
      indent(
        generateVariablesCode(proof) +
          "\n\n" +
          generateTheoremCode(name, proof)
      ) +
      "\n}"

  /**
   * Parse and check that a generated theorem file is valid, i.e. that it compiles and the theorem is proven
   * @param fileContent content of the generated file
   * @return true if the file is valid, false otherwise
   */
  def checkGeneratedFileContent(fileContent: String): Boolean =
    // TODO
    false

}
