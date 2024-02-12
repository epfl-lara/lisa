package lisa.utils

import lisa.kernel.proof.SequentCalculus.*
import lisa.utils.K
import lisa.utils.KernelHelpers.lambda
import lisa.prooflib.ProofTacticLib.*
import lisa.fol.FOL as F
import lisa.fol.FOLHelpers.*

object ProofsConverter {

// TODO: remove unnecessary variables "val s_..." in generated proofs -> need to keep track of which steps are used in other steps
// TODO: generate more realistic variable names
// TODO: handle automatic global variable declaration before theorems/proofs

  private def indent(s: String, indent: Int = 2): String = s.split("\n").map(" " * indent + _).mkString("\n")
  private def unindent(s: String, indent: Int = 2): String = s.split("\n").map(_.drop(indent)).mkString("\n")

  private def any2code(a: K.Sequent | K.Formula | K.Term): String = (a match
    case sq: K.Sequent => asFront(sq)
    case form: K.Formula => asFront(form)
    case term: K.Term => asFront(term)
  ).toString.replace("⇒", "==>").replace("⇔", "<=>")

  def scproof2code(p: K.SCProof): String = {
    def scproof2codeAux(p: K.SCProof, varPrefix: String = "s", premises: Seq[String] = Seq.empty): String = {
      def scproofstep2code(ps: SCProofStep, stepNum: Int, premises: Seq[String], varPrefix: String): String = {

        def index2stepvar(i: Int): String =
          if i < -premises.size then throw new Exception(s"step $i is not defined")
          else if i < 0 then premises(-i - 1)
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
            val (bot_, step_ref_seq) = (ps match
              case Restate(bot, t1) =>
                opening = ".from("
                (bot, Seq(t1))
              case RestateTrue(bot) =>
                tacticName = "Restate"
                (bot, null)
              case Hypothesis(bot, phi) => (bot, null)
              case Cut(bot, t1, t2, phi) => (bot, Seq(t1, t2))
              case LeftAnd(bot, t1, phi, psi) => (bot, Seq(t1))
              case LeftOr(bot, t, disjuncts) => (bot, t)
              case LeftImplies(bot, t1, t2, phi, psi) => (bot, Seq(t1, t2))
              case LeftIff(bot, t1, phi, psi) => (bot, Seq(t1))
              case LeftNot(bot, t1, phi) => (bot, Seq(t1))
              case LeftForall(bot, t1, phi, x, t) => (bot, Seq(t1))
              case LeftExists(bot, t1, phi, x) => (bot, Seq(t1))
              case LeftExistsOne(bot, t1, phi, x) => (bot, Seq(t1))
              case RightAnd(bot, t, conjuncts) => (bot, t)
              case RightOr(bot, t1, phi, psi) => (bot, Seq(t1))
              case RightImplies(bot, t1, phi, psi) => (bot, Seq(t1))
              case RightIff(bot, t1, t2, phi, psi) => (bot, Seq(t1, t2))
              case RightNot(bot, t1, phi) => (bot, Seq(t1))
              case RightForall(bot, t1, phi, x) => (bot, Seq(t1))
              case RightExists(bot, t1, phi, x, t) => (bot, Seq(t1))
              case RightExistsOne(bot, t1, phi, x) => (bot, Seq(t1))
              case Weakening(bot, t1) => (bot, Seq(t1))
              case LeftRefl(bot, t1, phi) => (bot, Seq(t1))
              case RightRefl(bot, phi) => (bot, null)
              case LeftSubstEq(bot, t1, equals, lambdaPhi) =>
                tacticName = s"LeftSubstEq.withParametersSimple(List(${equals
                    .map((a, b) => s"((${any2code(a.body)}), (${any2code(b.body)}))")
                    .mkString(", ")}), lambda(Seq(${lambdaPhi._1.map(asFrontLabel).mkString(", ")}), ${any2code(lambdaPhi._2)}))"
                (bot, Seq(t1))
              case RightSubstEq(bot, t1, equals, lambdaPhi) =>
                tacticName = s"RightSubstEq.withParametersSimple(List(${equals
                    .map((a, b) => s"((${any2code(a.body)}), (${any2code(b.body)}))")
                    .mkString(", ")}), lambda(Seq(${lambdaPhi._1.map(asFrontLabel).mkString(", ")}), ${any2code(lambdaPhi._2)}))"
                (bot, Seq(t1))
              case LeftSubstIff(bot, t1, equals, lambdaPhi) =>
                tacticName = s"LeftSubstIff.withParametersSimple(List(${equals
                    .map((a, b) => s"((${any2code(a.body)}), (${any2code(b.body)}))")
                    .mkString(", ")}), lambda(Seq(${lambdaPhi._1.map(asFrontLabel).mkString(", ")}), ${any2code(lambdaPhi._2)}))"
                (bot, Seq(t1))
              case RightSubstIff(bot, t1, equals, lambdaPhi) =>
                tacticName = s"RightSubstIff.withParametersSimple(List(${equals
                    .map((a, b) => s"((${any2code(a.body)}), (${any2code(b.body)}))")
                    .mkString(", ")}), lambda(Seq(${lambdaPhi._1.map(asFrontLabel).mkString(", ")}), ${any2code(lambdaPhi._2)}))"
                (bot, Seq(t1))
              case InstSchema(bot, t1, mCon, mPred, mTerm) =>
                if mCon.isEmpty && mPred.isEmpty then
                  tacticName = s"InstFunSchema(Map(${mTerm.toList
                      .map((k, v) => s"${asFrontLabel(k)} -> ${any2code(v.body)}")
                      .mkString(", ")}))"
                  (bot, Seq(t1))
                else if mCon.isEmpty && mTerm.isEmpty then
                  tacticName = s"InstPredSchema(Map(${mPred.toList
                      .map((k, v) => s"${asFrontLabel(k)} -> ${any2code(v.body)}")
                      .mkString(", ")}))"
                  (bot, Seq(t1))
                else throw new Exception("InstSchema not implemented")
              case _ => throw new Exception(s"Tactic ${ps.getClass.getName} not implemented")
            )

            indent(
              s"val ${varPrefix}_$stepNum = " + (
                if (step_ref_seq != null && step_ref_seq.size == 1 && stepNum > 0 && step_ref_seq.head + 1 == stepNum)
                then s"thenHave(${any2code(bot_)}) by $tacticName"
                else
                  s"have(${any2code(bot_)}) by $tacticName" + (
                    if step_ref_seq == null then ""
                    else s"$opening${step_ref_seq.map(index2stepvar).mkString(", ")}$closing"
                  )
              )
            )
      }

      p.steps.zipWithIndex.map((ps, i) => scproofstep2code(ps, i, premises, varPrefix)).mkString("\n")
    }
    unindent(scproof2codeAux(p))
  }

  def generateTheoremCode(name: String, statement: K.Sequent, proof: K.SCProof): String = {
    s"val $name = Theorem(\n" +
      indent(any2code(statement)) +
      s"\n) {\n" +
      indent(scproof2code(proof)) +
      s"\n}"
  }

}
