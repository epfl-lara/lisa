package lisa

import lisa.SetTheoryLibrary
import lisa.hol.HOLSteps
import lisa.utils.fol.FOL.{_, given}
import lisa.utils.prooflib.BasicMain
import lisa.utils.prooflib.OutputManager

import SetTheoryLibrary._

/**
 * The parent trait of all theory files containing mathematical development
 */
trait _HOL extends BasicMain {

  val F: lisa.utils.fol.FOL.type = lisa.utils.fol.FOL
  export F.{=== as _, ≠ as _, *, given}
  export lisa.maths.SetTheory.Functions.Predef.{*}
  export lisa.maths.SetTheory.Types.TypingHelpers.{main => _, fun => _, *, given}
  export lisa.hol.VarsAndFunctions.{
    fun,
    computeType,
    eqOne,
    tforall,
    TypedForall,
    TypedVariable,
    holeq,
    HOLSequent,
    =:=,
    getContext,
    typedvar,
    typevar,
    given_Conversion_TypedForall_Expr,
    given_Conversion_Expr_HOLSequent,
    given_Conversion_Expr_Expr,
    termToSetConv,
    setTermToSetConv
  }
  export lisa.hol.HOLHelperTheorems.{𝔹, Zero, One, =:=}
  export lisa.maths.SetTheory.Types.Tactics.Typecheck.*
  
  val library: SetTheoryLibrary.type = SetTheoryLibrary
  given SetTheoryLibrary.type = library

  // def assume(using proof: library.Proof)(t: Expr[Ind]): proof.ProofStep =
  //  library.assume(eqOne(t))

  def withCTX(s: F.Sequent): F.Sequent =
    s ++<? (getContext(s) |- ())

  // HOLTheorem is now just an alias for regular Theorem since types are managed externally
  def HOLTheorem(using om: OutputManager, name: sourcecode.FullName, line: sourcecode.Line, file: sourcecode.File)(statement: F.Sequent)(computeProof: Proof ?=> Unit): THM =
    val ctx = getContext(statement)
    SetTheoryLibrary.Theorem(using om, name, line, file)(statement ++<< (ctx |- ()))(computeProof)

}

trait HOL extends _HOL {
  // export lisa.hol.HOLSteps.*
  export SetTheoryLibrary.{library => _, have => _, given, _}
  export lisa.utils.prooflib.BasicStepTactic.*
  export lisa.utils.prooflib.SimpleDeducedSteps.*

  export lisa.automation.Tautology
  export lisa.automation.Substitution
  export lisa.automation.Tableau

  def HOLassume(using proof: library.Proof)(t: Expr[Ind]): proof.ProofStep =
    val f = eqOne(t)
    library.assume(f)
    val ctx = getContext(t)
    // ctx.foreach(ta => assume(ta))
    library.have((ctx |- f) +<< f) by Restate

  def have(using proof: library.Proof)(res: Sequent): HaveSequent =
    val ctx = getContext(res)
    HaveSequent(res ++<< (ctx |- ()))

  def have(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(v: proof.Fact | proof.ProofTacticJudgement) = v match {
    case judg: proof.ProofTacticJudgement => judg.validate(line, file)
    case fact: proof.Fact @unchecked => HaveSequent(proof.sequentOfFact(fact)).by(using proof, line, file)(Weakening(using library, proof)(fact))
  }

  // ─── HOL Tactic wrappers with integrated `have` ───

  /** REFL: |- t = t */
  def REFL(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(t: Expr[Ind]) = 
    have(HOLSteps._REFL(t))

  /** TRANS: |- s = t, |- t = u  ==>  |- s = u */
  def TRANS(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(t1: proof.Fact, t2: proof.Fact) = 
    have(HOLSteps._TRANS(t1, t2))

  /** MK_COMB: |- f = g, |- x = y  ==>  |- f x = g y */
  def MK_COMB(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(f1: proof.Fact, f2: proof.Fact) = 
    have(HOLSteps._MK_COMB(f1, f2))

  /** ABS: |- t = u  ==>  |- λx. t = λx. u */
  def ABS(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(x: TypedVariable)(prem: proof.Fact) = 
    have(HOLSteps._ABS(x)(prem))

  /** BETA_CONV: (λx. t) u  ==>  |- (λx. t) u = t[x := u] */
  def BETA_CONV(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(t: Expr[Ind]) = 
    have(HOLSteps._BETA_CONV(t))

  /** BETA: (λx. t) x  ==>  |- (λx. t) x = t */
  def BETA(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(t: Expr[Ind]) = 
    have(HOLSteps._BETA(t))

  /** ETA: |- λx. f x = f (when x not free in f) */
  def ETA(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(x: TypedVariable, t: Expr[Ind]) = 
    have(HOLSteps._ETA(x, t))

  /** ASSUME: t |- t */
  def ASSUME(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(t: Expr[Ind]) = 
    have(HOLSteps._ASSUME(t))

  /** EQ_MP: |- t = u, |- t  ==>  |- u */
  def EQ_MP(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(eq: proof.Fact, p: proof.Fact) = 
    have(HOLSteps._EQ_MP(eq, p))

  /** DEDUCT_ANTISYM_RULE: A |- p, B |- q  ==>  A - p, B - q |- p = q */
  def DEDUCT_ANTISYM_RULE(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(t1: proof.Fact, t2: proof.Fact) = 
    have(HOLSteps._DEDUCT_ANTISYM_RULE(t1, t2))

  /** INST: Instantiate term variables in a theorem */
  def INST(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(inst: Seq[(Variable[Ind], Expr[Ind])], prem: proof.Fact) = 
    have(HOLSteps._INST(inst, prem))

  /** INST_TYPE: Instantiate type variables in a theorem */
  def INST_TYPE(using line: sourcecode.Line, file: sourcecode.File)(using proof: library.Proof)(inst: Seq[(Variable[Ind], Expr[Ind])], prem: proof.Fact) = 
    have(HOLSteps._INST_TYPE(inst, prem))

}
