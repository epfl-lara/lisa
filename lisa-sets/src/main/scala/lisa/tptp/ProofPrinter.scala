package lisa.tptp

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

  def sequentToFOFAnnotated(sequent: K.Sequent, name: String, role: String, annotations: Annotations = None): FOFAnnotated = {
    val state = sequentToFOFStatement(sequent)
    FOFAnnotated(name, role, state, annotations)
  }

  def sequentToFOFStatement(sequent: K.Sequent): FOF.Statement = {
    if sequent.left.isEmpty && sequent.right.size == 1 then 
      FOF.Logical(formulaToFOFFormula(sequent.right.head, Set()))
    else
      FOF.Sequent(sequent.left.map(formulaToFOFFormula(_, Set())).toSeq, sequent.right.map(formulaToFOFFormula(_, Set())).toSeq)
  }

  def isLowerWord(s: String): Boolean = s.head.isLower && s.tail.forall(_.isLetterOrDigit)
  inline def quoted(s: String): String = if isLowerWord(s) then s else s"'$s'"

  def termToFOFTerm(term: K.Expression, bound: Set[K.Identifier]): FOF.Term = {
    term match {
      case K.Variable(id, K.Ind) => 
        if bound.contains(id) then FOF.Variable("X" + id)
        else FOF.Variable(quoted("s" + id))
      case K.Constant(id, K.Ind) => FOF.AtomicTerm(quoted("c" + id), Seq())
      case K.Multiapp(K.Constant(id, typ), args) =>
        FOF.AtomicTerm(quoted("c" + id), args.map(termToFOFTerm(_, bound)))
      case K.Multiapp(K.Variable(id, typ), args) =>
        FOF.AtomicTerm(quoted("s" + id), args.map(termToFOFTerm(_, bound)))
      case K.Epsilon(v, f) => throw new Exception("Epsilon terms are not supported")
      case _ => throw new Exception("The expression is not purely first order:\n" + term.repr)
    }
  }
  def formulaToFOFFormula(formula: K.Expression, bound: Set[K.Identifier]): FOF.Formula = {
    formula match
      case K.equality(left, right) =>
        FOF.Equality(termToFOFTerm(left, bound), termToFOFTerm(right, bound))
      case K.top => FOF.AtomicFormula("$true", Seq())
      case K.bot => FOF.AtomicFormula("$false", Seq())
      case K.neg(f) => FOF.UnaryFormula(FOF.~, formulaToFOFFormula(f, bound))
      case K.and(f1, f2) => FOF.BinaryFormula(FOF.&, formulaToFOFFormula(f1, bound), formulaToFOFFormula(f2, bound))
      case K.or(f1, f2) => FOF.BinaryFormula(FOF.|, formulaToFOFFormula(f1, bound), formulaToFOFFormula(f2, bound))
      case K.implies(f1, f2) => FOF.BinaryFormula(FOF.Impl, formulaToFOFFormula(f1, bound), formulaToFOFFormula(f2, bound))
      case K.iff(f1, f2) => FOF.BinaryFormula(FOF.<=>, formulaToFOFFormula(f1, bound), formulaToFOFFormula(f2, bound))
      case K.forall(K.Lambda(v, f)) => FOF.QuantifiedFormula(FOF.!, Seq("X" + v.id), formulaToFOFFormula(f, bound + v.id))
      case K.exists(K.Lambda(v, f)) => FOF.QuantifiedFormula(FOF.?, Seq("X" + v.id), formulaToFOFFormula(f, bound + v.id))
      case K.forall(p) =>
        val x = K.freshId(p.freeVariables.map(_.id), "x")
        FOF.QuantifiedFormula(FOF.!, Seq("X" + x), formulaToFOFFormula(K.Application(p, K.Variable(x, K.Ind)), bound + x))
      case K.exists(p) =>
        val x = K.freshId(p.freeVariables.map(_.id), "x")
        FOF.QuantifiedFormula(FOF.?, Seq("X" + x), formulaToFOFFormula(K.Application(p, K.Variable(x, K.Ind)), bound + x))
      case K.Multiapp(K.Constant(id, typ), args) =>
        FOF.AtomicFormula(quoted("c" + id), args.map(termToFOFTerm(_, bound)))
      case K.Multiapp(K.Variable(id, typ), args) =>
        FOF.AtomicFormula(quoted("s" + id), args.map(termToFOFTerm(_, bound)))
      case _ => throw new Exception("The expression is not purely first order: " + formula)
        
  }

  def formulaToFOFStatement(formula: K.Expression): FOF.Statement = {
    FOF.Logical(formulaToFOFFormula(formula, Set()))
  }


  def proofToTPTP(proof: K.SCProof, axioms: Map[Int, (String, K.Sequent)], conj: (String, K.Sequent)): Seq[FOFAnnotated] = {
    val tptpaxioms = axioms.map {
      case (i, (name, sequent)) => sequentToFOFAnnotated(sequent, name, "axiom", None)
    }.toSeq
    val middle = proof.steps.zipWithIndex.map((s, no) => proofStepToTPTP(s, axioms, no))

    val end = sequentToFOFAnnotated(conj._2, conj._1, "conjecture", None)

    tptpaxioms ++ middle :+ end
  }


  def s(no:Int): String = "s" + no

  def premisesToAnnotations(premises: Seq[Int], stepName: String) = {
    Some(
      (
        GeneralTerm(
          List(
            MetaFunctionData(
              "inference",
              List(
                GeneralTerm(List(MetaFunctionData(stepName, List())), None), // stepnames
                GeneralTerm(List(), Some(List(GeneralTerm(List(MetaFunctionData("status", List(Inference.String("thm")))), None)))), // params
                GeneralTerm(List(), Some(premises.map(n => Inference.String(s(n)))))
              ) // numbers
            )
          ),
          None
        ),
        None
      )
    )
  }

  def proofStepToTPTP(step: K.SCProofStep, axiomsMap: Map[Int, (String, K.Sequent)], no: Int): FOFAnnotated = {
    val role = "plain"

    step match
      case K.Beta(bot, t1) => 
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "beta"))
      case K.Cut(bot, t1, t2, phi) => 
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1, t2), "cut"))
      case K.Hypothesis(bot, phi) => 
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(), "hyp"))
      case K.InstSchema(bot, t1, subst) => 
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "inst_schema"))
      case K.LeftAnd(bot, t1, phi, psi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "left_and"))
      case K.LeftExists(bot, t1, phi, x) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "left_exists"))
      case K.LeftForall(bot, t1, phi, x, t) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "left_forall"))
      case K.LeftIff(bot, t1, phi, psi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "left_iff"))
      case K.LeftImplies(bot, t1, t2, phi, psi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1, t2), "left_implies"))
      case K.LeftNot(bot, t1, phi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "left_not"))
      case K.LeftOr(bot, t, disjuncts) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(t, "left_or"))
      case K.LeftRefl(bot, t1, fa) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "left_refl"))
      case K.LeftSubstEq(bot, t1, equals, lambdaPhi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "left_subst_eq"))
      case K.Restate(bot, t1) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "restate"))
      case K.RestateTrue(bot) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(), "restate_true"))
      case K.RightAnd(bot, t, cunjuncts) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(t, "right_and"))
      case K.RightEpsilon(bot, t1, phi, x, t) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "right_epsilon"))
      case K.RightExists(bot, t1, phi, x, t) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "right_exists"))
      case K.RightForall(bot, t1, phi, x) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "right_forall"))
      case K.RightIff(bot, t1, t2, phi, psi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1, t2), "right_iff"))
      case K.RightImplies(bot, t1, phi, psi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "right_implies"))
      case K.RightNot(bot, t1, phi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "right_not"))
      case K.RightOr(bot, t1, phi, psi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "right_or"))
      case K.RightRefl(bot, fa) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(), "right_refl"))
      case K.RightSubstEq(bot, t1, equals, lambdaPhi) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "right_subst_eq"))
      case K.SCSubproof(sp, premises) => 
        sequentToFOFAnnotated(step.bot, s(no), role, premisesToAnnotations(premises, "subproof"))
      case K.Sorry(bot) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(), "sorry"))
      case K.Weakening(bot, t1) =>
        sequentToFOFAnnotated(bot, s(no), role, premisesToAnnotations(Seq(t1), "weakening"))
  }

}
