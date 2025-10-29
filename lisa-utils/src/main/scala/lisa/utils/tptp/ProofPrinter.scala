package lisa.tptp
import KernelParser.unsanitize
import leo.datastructures.TPTP.AnnotatedFormula
import leo.datastructures.TPTP.FOF
import leo.datastructures.TPTP.FOFAnnotated
import leo.datastructures.TPTP.FOTAnnotated
import leo.modules.input.{TPTPParser => Parser}
import lisa.utils.K
import K.{given}
import K.{repr, -<<, +<<, ->>, +>>, |-}

import java.io.File

import Parser.TPTPParseException
import ProofParser.*
import leo.datastructures.TPTP.{Annotations, GeneralTerm, MetaFunctionData, NumberData, Integer, FOF, GeneralFormulaData, FOTData, FOFData}


object ProofPrinter {

  def problemToFile(fileDirectory: String, fileName: String, name: String, axioms: Seq[K.Sequent], conjecture: K.Sequent, source: String): File = {
    // case class Problem(file: String, domain: String, name: String, status: String, spc: Seq[String], formulas: Seq[AnnotatedStatement])
    val file = new File(fileDirectory + fileName + ".p")
    // val fileName = originFile.split("/").last
    val header =
      s"""%--------------------------------------------------------------------------
% File     : $fileName : $TPTPversion.
% Domain   : None
% Problem  : ${name}
% Version  : None
% English  :

% Refs     : https://github.com/epfl-lara/lisa
%          : lisa.utils.tptp.ProofParser
% Source   : [Lisa, $source]
% Names    : 

% Status   : Unknown
% Rating   : ?
% Syntax   : ?
% SPC      : FOF_UNK_RFO_SEQ

% Comments : This problem, was printed from a statement in a proof of a theorem by the Lisa theorem prover for submission to proof-producing ATPs.
%--------------------------------------------------------------------------
"""
    val writer = new java.io.PrintWriter(file)
    writer.write(header)
    var counter = 0
    def nextc = { counter += 1; counter }
    axioms.foreach(s => writer.write(sequentToFOFAnnotated(s, "a" + nextc, "axiom").pretty + "\n"))
    writer.write(sequentToFOFAnnotated(conjecture, "c" + nextc, "conjecture").pretty + "\n\n")
    writer.close()
    file
  }

  def sequentToFOFAnnotated(sequent: K.Sequent, name: String, role: String, annotations: Annotations = None, strict: Boolean = false): FOFAnnotated = {
    val state = sequentToFOFStatement(sequent, strict)
    FOFAnnotated(name, role, state, annotations)
  }

  def sequentToFOFStatement(sequent: K.Sequent, strict: Boolean = false): FOF.Statement = {
    if sequent.left.isEmpty && sequent.right.size == 1 then
      FOF.Logical(formulaToFOFFormula(sequent.right.head, Set(), strict))
    else
      FOF.Sequent(sequent.left.map(formulaToFOFFormula(_, Set(), strict)).toSeq, sequent.right.map(formulaToFOFFormula(_, Set(), strict)).toSeq)
  }

  def isLowerWord(s: String): Boolean = s.head.isLower && s.tail.forall(_.isLetterOrDigit)
  inline def quoted(s: String): String = if isLowerWord(s) then s else s"'$s'"

  /**
    * 
    *
    * @param term
    * @param bound
    * @param strict if true, the term is printed as-is without any transformation on names
    */
  def termToFOFTerm(term: K.Expression, bound: Set[K.Identifier], strict:Boolean = false): FOF.Term = {
    term match {
      case K.Variable(id, K.Ind) => 
        if strict then
          if id.name(0).isUpper then FOF.Variable(unsanitize(id))
          else FOF.Variable(unsanitize("X"+id))
        else if bound.contains(id) then FOF.Variable("X" + id)
        else FOF.Variable(quoted("s" + id))
      case K.Constant(id, K.Ind) => 
        if strict then
          if id.name(0).isLower && !id.name.contains(" ") then FOF.AtomicTerm(unsanitize(id), Seq())
          else FOF.AtomicTerm(quoted(unsanitize(id)), Seq())
        else FOF.AtomicTerm(quoted("c" + id), Seq())
      case K.Multiapp(K.Constant(id, typ), args) =>
        if strict then
          if id.name(0).isLower && !id.name.contains(" ") then FOF.AtomicTerm(unsanitize(id), args.map(termToFOFTerm(_, bound, strict)))
          else FOF.AtomicTerm(quoted(unsanitize(id)), args.map(termToFOFTerm(_, bound, strict)))
        else FOF.AtomicTerm(quoted("c" + id), args.map(termToFOFTerm(_, bound, strict)))
      case K.Multiapp(K.Variable(id, typ), args) =>
        if strict then
          FOF.AtomicTerm("`" + unsanitize(id), args.map(termToFOFTerm(_, bound, strict)))
        else FOF.AtomicTerm(quoted(unsanitize("s" + id)), args.map(termToFOFTerm(_, bound)))
      case K.Epsilon(v, f) => throw new Exception("Epsilon terms are not supported")
      case _ => throw new Exception("The expression is not purely first order:\n" + term.repr)
    }
  }
  
  def formulaToFOFFormula(formula: K.Expression, bound: Set[K.Identifier], strict:Boolean = false): FOF.Formula = {
    formula match
      case K.equality(left, right) =>
        FOF.Equality(termToFOFTerm(left, bound, strict), termToFOFTerm(right, bound, strict))
      case K.top => FOF.AtomicFormula("$true", Seq())
      case K.bot => FOF.AtomicFormula("$false", Seq())
      case K.neg(f) => FOF.UnaryFormula(FOF.~, formulaToFOFFormula(f, bound, strict))
      case K.and(f1, f2) => FOF.BinaryFormula(FOF.&, formulaToFOFFormula(f1, bound, strict), formulaToFOFFormula(f2, bound, strict))
      case K.or(f1, f2) => FOF.BinaryFormula(FOF.|, formulaToFOFFormula(f1, bound, strict), formulaToFOFFormula(f2, bound, strict))
      case K.implies(f1, f2) => FOF.BinaryFormula(FOF.Impl, formulaToFOFFormula(f1, bound, strict), formulaToFOFFormula(f2, bound, strict))
      case K.iff(f1, f2) => FOF.BinaryFormula(FOF.<=>, formulaToFOFFormula(f1, bound, strict), formulaToFOFFormula(f2, bound, strict))
      case K.forall(K.Lambda(v, f)) => 
        val x = if strict then unsanitize(v.id) else unsanitize("X"+v.id)
        FOF.QuantifiedFormula(FOF.!, Seq(x), formulaToFOFFormula(f, bound + v.id, strict))
      case K.exists(K.Lambda(v, f)) =>
        val x = if strict then unsanitize(v.id) else unsanitize("X"+v.id)
        FOF.QuantifiedFormula(FOF.?, Seq(x), formulaToFOFFormula(f, bound + v.id, strict))
      case K.forall(p) =>
        val x = K.freshId(p.freeVariables.map(_.id), "x")
        FOF.QuantifiedFormula(FOF.!, Seq(if strict then unsanitize(x) else "X" + x), formulaToFOFFormula(K.Application(p, K.Variable(x, K.Ind)), bound + x, strict))
      case K.exists(p) =>
        val x = K.freshId(p.freeVariables.map(_.id), "x")
        FOF.QuantifiedFormula(FOF.?, Seq(if strict then unsanitize(x) else "X" + x), formulaToFOFFormula(K.Application(p, K.Variable(x, K.Ind)), bound + x, strict))
      case K.Multiapp(K.Constant(id, typ), args) =>
        if strict then 
          if id.name(0).isLower then FOF.AtomicFormula(unsanitize(id), args.map(termToFOFTerm(_, bound, strict)))
          else FOF.AtomicFormula(quoted(unsanitize(id)), args.map(termToFOFTerm(_, bound, strict)))
        else FOF.AtomicFormula(quoted("c" + id), args.map(termToFOFTerm(_, bound, strict)))
      case K.Multiapp(K.Variable(id, typ), args) =>
        if strict then
          FOF.AtomicFormula("`" + unsanitize(id), args.map(termToFOFTerm(_, bound, strict)))
        else FOF.AtomicFormula(quoted("s" + id), args.map(termToFOFTerm(_, bound, strict)))
      case K.Constant(id, typ) =>
        if strict then
          if id.name(0).isLower then FOF.AtomicFormula(unsanitize(id), Seq())
          else FOF.AtomicFormula(unsanitize(id), Seq())
        else FOF.AtomicFormula(quoted("p" + id), Seq())
      case _ => throw new Exception("The expression is not purely first order: " + formula)
        
  }

  def formulaToFOFStatement(formula: K.Expression): FOF.Statement = {
    FOF.Logical(formulaToFOFFormula(formula, Set()))
  }


  def proofToTPTP(proof: K.SCProof, axioms: Map[Int, (String, K.Sequent)], conj: (String, K.Sequent), strict: Boolean = false): Seq[FOFAnnotated] = {
    val tptpaxioms = axioms.map {
      case (i, (name, sequent)) => sequentToFOFAnnotated(sequent, name, "axiom", None, strict)
    }.toSeq
    val middle = proof.steps.zipWithIndex.map((step, no) => proofStepToTPTP(step, axioms, no, strict))

    val conjec = sequentToFOFAnnotated(conj._2, conj._1, "conjecture", None, strict)

    (tptpaxioms /*:+ conjec*/) ++ middle 
  }


  def s(no:Int): String = "s" + no

  def premisesToAnnotationsStr(premises: Seq[String], stepName: String) = {
    Some(
      (
        GeneralTerm(
          List(
            MetaFunctionData(
              "inference",
              List(
                GeneralTerm(List(MetaFunctionData(stepName, List())), None), // stepnames
                GeneralTerm(List(), Some(List(GeneralTerm(List(MetaFunctionData("status", List(Inference.String("thm")))), None)))), // params
                GeneralTerm(List(), Some(premises.map(n => Inference.String(n))))
              ) // numbers
            )
          ),
          None
        ),
        None
      )
    )
  }

  def premisesToAnnotations(premises: Seq[Int], stepName: String): Annotations = 
    premisesToAnnotationsStr(premises.map(s), stepName)


  def proofStepToTPTP(step: K.SCProofStep, axiomsMap: Map[Int, (String, K.Sequent)], no: Int, strict: Boolean): FOFAnnotated = {
    val role = "plain"

    step match
      case K.Beta(bot, t1) => 
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "beta"), strict)
      case K.Cut(bot, t1, t2, phi) => 
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1, t2), "cut"), strict)
      case K.Hypothesis(bot, phi) => 
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(), "hyp"), strict)
      case K.InstSchema(bot, t1, subst) => 
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "inst_schema"), strict)
      case K.LeftAnd(bot, t1, phi, psi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "left_and"), strict)
      case K.LeftExists(bot, t1, phi, x) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "left_exists"), strict)
      case K.LeftForall(bot, t1, phi, x, t) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "left_forall"), strict)
      case K.LeftIff(bot, t1, phi, psi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "left_iff"), strict)
      case K.LeftImplies(bot, t1, t2, phi, psi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1, t2), "left_implies"), strict)
      case K.LeftNot(bot, t1, phi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "left_not"), strict)
      case K.LeftOr(bot, t, disjuncts) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(t, "left_or"), strict)
      case K.LeftRefl(bot, t1, fa) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "left_refl"), strict)
      case K.LeftSubstEq(bot, t1, equals, lambdaPhi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "left_subst_eq"), strict)
      case K.Restate(bot, t1) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "restate"), strict)
      case K.RestateTrue(bot) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(), "restate_true"), strict)
      case K.RightAnd(bot, t, cunjuncts) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(t, "right_and"), strict)
      case K.RightEpsilon(bot, t1, phi, x, t) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "right_epsilon"), strict)
      case K.RightExists(bot, t1, phi, x, t) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "right_exists"), strict)
      case K.RightForall(bot, t1, phi, x) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "right_forall"), strict)
      case K.RightIff(bot, t1, t2, phi, psi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1, t2), "right_iff"), strict)
      case K.RightImplies(bot, t1, phi, psi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "right_implies"), strict)
      case K.RightNot(bot, t1, phi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "right_not"), strict)
      case K.RightOr(bot, t1, phi, psi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "right_or"), strict)
      case K.RightRefl(bot, fa) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(), "right_refl"), strict)
      case K.RightSubstEq(bot, t1, equals, lambdaPhi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "right_subst_eq"), strict)
      case K.SCSubproof(sp, premises) =>
        sequentToFOFAnnotated(step.bot, s(no), role, premisesToAnnotations(premises, "subproof"), strict)
      case K.Sorry(bot) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(), "sorry"), strict)
      case K.Weakening(bot, t1) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "weakening"), strict)
  }

}
