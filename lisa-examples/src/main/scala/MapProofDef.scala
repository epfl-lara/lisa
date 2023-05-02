import lisa.automation.kernel.OLPropositionalSolver.*
import lisa.automation.kernel.SimpleSimplifier.*
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProofChecker.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.mathematics.SetTheory.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.*
import lisa.utils.FOLPrinter.*
import lisa.utils.KernelHelpers.checkProof
import lisa.utils.parsing.FOLPrinter
import lisa.utils.unification.UnificationUtils.*

object MapProofDef extends lisa.Main{
  val self = this

  val x = variable
  val y = variable
  val xs = variable
  val ys = variable
  val f = variable



  val Nil = ConstantFunctionLabel("Nil", 0)()
  theory.addSymbol(ConstantFunctionLabel("Nil", 0))
  val Cons = ConstantFunctionLabel("Cons", 2)
  theory.addSymbol(Cons)

  class TermProxy(t1:Term) {
    infix def ::(t2: Term) = Cons(t2, t1)
    infix def +++(t2: Term) = append(t1, t2)
    def map(t2: Term) = self.map(t1, t2)
    def mapTr(t2: Term, t3: Term) = self.mapTr(t1, t2, t3)
  }
  given Conversion[Term, TermProxy] = TermProxy(_)
  given Conversion[VariableLabel, TermProxy] = v => TermProxy(v())

  object append {
    val append_ = ConstantFunctionLabel("append", 2)
    theory.addSymbol(append_)
    
    val NilCase = theory.addAxiom("append.NilCase", (Nil +++ xs) === xs).get
    val ConsCase = theory.addAxiom("append.ConsCase", ((x :: xs) +++ ys) === Cons(x, append(xs, ys))).get
    
    def apply(t1: Term, t2: Term) = append_(t1, t2)
  }

  object map {
    val map = ConstantFunctionLabel("map", 2)
    theory.addSymbol(map)
    val NilCase = theory.addAxiom("map.NilCase", Nil.map(f) === Nil).get
    val ConsCase = theory.addAxiom("map.ConsCase", (x :: xs).map(f) === (app(f, x) :: xs.map(f))).get
    def apply(t1: Term, t2: Term) = map(t1, t2)
  }

  object mapTr {
    val mapTr = ConstantFunctionLabel("mapTr", 3)
    theory.addSymbol(mapTr)
    val NilCase = theory.addAxiom("mapTr.NilCase", Nil.mapTr(f, xs) === xs).get
    val ConsCase = theory.addAxiom("mapTr.ConsCase", (x :: xs).mapTr(f, ys) === xs.mapTr(f, ys +++ (app(f, x) :: Nil))).get
    def apply(t1: Term, t2: Term, t3: Term) = mapTr(t1, t2, t3)
  }



  // some more DSL

  val mapRules = Seq(
    map.NilCase,
    map.ConsCase,
    mapTr.NilCase,
    mapTr.ConsCase,
    append.NilCase,
    append.ConsCase
  )

  object Auto extends ProofTactic {

    def apply(using lib: lisa.prooflib.Library, proof: lib.Proof)
         (args: proof.Fact | RunningTheory#Justification)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement = {
      val tac: proof.ProofTacticJudgement = Substitution.apply2(false, args)(premise)(bot)
      tac match {
        case proof.ValidProofTactic(a, b) => proof.ValidProofTactic(a, b)
        case proof.InvalidProofTactic(m1) =>
          val tac: proof.ProofTacticJudgement = Substitution.apply2(true, args)(premise)(bot)
          tac match {
            case proof.ValidProofTactic(a, b) => proof.ValidProofTactic(a, b)
            case proof.InvalidProofTactic(m2) =>
              val tac: proof.ProofTacticJudgement = Tautology.from(args.asInstanceOf, premise)(bot)
              tac match {
                case proof.ValidProofTactic(a, b) => proof.ValidProofTactic(a, b)
                case proof.InvalidProofTactic(m3) => proof.InvalidProofTactic("Decomposition of Auto failure:\n" + m1 + "\n" + m2 + "\n" + m3)
              }
          }
      }
    }

    def a(using lib: lisa.prooflib.Library, proof: lib.Proof)
             (args: proof.Fact | RunningTheory#Justification)(bot: Sequent): proof.ProofTacticJudgement = {
      val tac: proof.ProofTacticJudgement = Tautology.from(args.asInstanceOf)(bot)
      tac match {
        case proof.ValidProofTactic(a, b) => proof.ValidProofTactic(a, b)
        case proof.InvalidProofTactic(m3) => proof.InvalidProofTactic("Decomposition of Auto failure:\n" + m3)
      }
    }
  }

}
