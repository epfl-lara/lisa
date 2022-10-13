import lisa.Main
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.proof.SCProofChecker.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.automation.kernel.SimplePropositionalSolver.solveSequent
import lisa.tptp.KernelParser.*
import lisa.tptp.ProblemGatherer.*
import lisa.tptp.*
import lisa.utils.Helpers.{show, *, given}
import lisa.utils.Printer.*
import lisa.utils.tactics.ProofStepLib.ProofStep

/**
 * Discover some of the elements of LISA to get started.
 */
object Example {
  def main(args: Array[String]): Unit = {

    proofExample() // uncomment when exercise finished
    // solverExample()
    // tptpExample()
  }

  /**
   * A little example of a small LISA proof with holes to fill as an exercise.
   * All interrogation marks have to be replaced by proof steps, (sets of) formulas or integers.
   * The last two lines don't need to be changed.
   */
  def proofExample(): Unit = {

    object Ex extends Main {
      /*
      THEOREM("fixedPointDoubleApplication") of "" PROOF {
        steps(
          ???,
          ???,
          ?????(Set(P(x), P(f(x)), P(f(x)) ==> P(f(f(x)))) |- P(f(f(x))), 1, 0, ????, ????),
          Hypothesis(Set(P(x), P(f(x)) ==> P(f(f(x)))) |- Set(P(x), P(f(f(x)))), P(x)),
          LeftImplies(???? |- ????, 3, 2, ????, ????),
          LeftForall(Set(????, ????, ????) |- ????, 4, ????, x, x),
          LeftForall(Set(????, ????) |- ????, 5, P(x) ==> P(f(x)), x, f(x)),
          RightImplies(forall(x, P(x) ==> P(f(x))) |- P(x) ==> P(f(f(x))), 6, P(x), P(f(f(x)))),
          RightForall(forall(x, P(x) ==> P(f(x))) |- forall(x, P(x) ==> P(f(f(x)))), 7, P(x) ==> P(f(f(x))), x)
        )
      } using ()
      show
      */

      THEOREM("weakeningTest") of "∀ ?x. set_membership(?x, ?X) ⊢ set_membership(?y, ?X)" NPROOF {

        val x = VariableLabel("x")
        val X = VariableLabel("X")
        val y = VariableLabel("y")

        // have(forall(x, in(x, X)) |- forall(x, in(x, X))) by Trivial
        // val s1 = have(forall(x, forall(X, in(x, X))) |- forall(x, forall(X, in(x, X)))) by Trivial
        // have(forall(x, in(x, X)) |- in(y, X)) by InstantiateForall(forall(x, in(x, X)), y)(0)
        // by InstantiateForall(forall(x, in(x, X)), y)(0)
        // have(forall(x, in(x, X)) |- in(y, X)) by InstantiateForall(y)(0)
        // by InstantiateForall(y)(0)
        // have(forall(x, forall(X, in(x, X))) |- in(y, x)) by InstantiateForall(forall(x, forall(X, in(x, X))), y, x)(1)
        // by InstantiateForall(forall(x, forall(X, in(x, X))), y, x)(1)
        // have(forall(x, forall(X, in(x, X))) |- in(y, x)) by InstantiateForall(y, x)(1)
        // by InstantiateForall(y, x)(1)
        // andThen(forall(x, forall(X, in(x, X))) |- Set(forall(x, forall(X, in(x, X))), in(y, x), in(x, y))) by Weakening
        // andThen(forall(x, forall(X, in(x, X))) |- forall(x, forall(X, in(x, X))) \/ in(y, x) \/ in(x, y)) by Rewrite
        // andThen(forall(x, forall(X, in(x, X))) |- Set(forall(x, forall(X, in(x, X))), in(y, x), in(x, y))) by Rewrite
        // andThen(Set(forall(x, forall(X, in(x, X))), in(x, X)) |- Set(forall(x, forall(X, in(x, X))), in(y, x), in(x, y))) by Weakening
        // andThen(forall(x, forall(X, in(x, X))) /\ in(x, X) |- Set(forall(x, forall(X, in(x, X))), in(y, x), in(x, y))) by Rewrite

        withImport(ax"EmptySet")
        have(() |- !in(x, emptySet())) by InstantiateForall(x)(-1)

        showCurrentProof()
      }
      show

      THEOREM("fixedPointDoubleApplication") of "∀ ?x. ?P(?x) ⇒ ?P(?f(?x)) ⊢ ∀ ?x. ?P(?x) ⇒ ?P(?f(?f(?x)))" NPROOF {
        assume(ax"extensionalityAxiom")
        withImport(ax"subsetAxiom")
        val n0 = have("?P(?x); ?P(?f(?x)); ?P(?f(?x)) ⇒ ?P(?f(?f(?x))) ⊢ ?P(?f(?f(?x)))")       by   Trivial
        val n1 = have(Set(P(x), P(f(x)) ==> P(f(f(x)))) |- Set(P(x), P(f(f(x)))))                    by   Trivial
        val n2 = have(Set(P(x), P(x) ==> P(f(x)), P(f(x)) ==> P(f(f(x)))) |- P(f(f(x))))             by   LeftImplies(P(x), P(f(x)))(n1, n0)
        have(Set(forall(x, P(x) ==> P(f(x))), P(x), P(f(x)) ==> P(f(f(x)))) |- P(f(f(x))) )          by   LeftForall(P(x) ==> P(f(x)), x, x)(n2)
        val test = andThen(Set(forall(x, P(x) ==> P(f(x))), P(x)) |- P(f(f(x))))                     by   LeftForall(P(x) ==> P(f(x)), x, f(x))

        showCurrentProof()

        assume(forall(x, P(x) ==> P(f(x))))
        have(() |- P(x) ==> P(f(f(x))))                                                              by   Trivial(test)
        andThen(() |- forall(x, P(x) ==> P(f(f(x)))))                                                by   RightForall(P(x) ==> P(f(f(x))), x)
        Discharge(ax"extensionalityAxiom")
      }
      show
      THEOREM("inclusionEquivalence") of "subset_of(?x, ?y) /\\ subset_of(?y, ?x) <-> ?x = ?y" NPROOF {

        val x = VariableLabel("x")
        val y = VariableLabel("y")
        val z = VariableLabel("z")

        withImport(ax"extensionalityAxiom")
        withImport(ax"subsetAxiom")
        val hypo = have("subset_of(?x, ?y) ; subset_of(?y, ?x) |- subset_of(?x, ?y) /\\ subset_of(?y, ?x)")  by Trivial
        
        have(() |- (subset(x, y) <=> forall(z, in(z, x) ==> in(z, y)))) by InstantiateForall(x, y)(-1)
        val subx = andThen(() |- (subset(x, y) ==> (forall(z, in(z, x) ==> in(z, y)))) /\ ((forall(z, in(z, x) ==> in(z, y))) ==> subset(x, y))) by Rewrite

        have(() |- (subset(y, x) <=> forall(z, in(z, y) ==> in(z, x)))) by InstantiateForall(y, x)(-1)
        val suby = andThen(() |- (subset(y, x) ==> (forall(z, in(z, y) ==> in(z, x)))) /\ ((forall(z, in(z, y) ==> in(z, x))) ==> subset(y, x))) by Rewrite

        val prem = Set(subset(x, y), subset(y, x))
        val excess = subset(x, y) /\ subset(y, x) /\ 
              (
                (subset(x, y) ==> (forall(z, in(z, x) ==> in(z, y)))) /\ ((forall(z, in(z, x) ==> in(z, y))) ==> subset(x, y))
              ) /\
              (
                (subset(y, x) ==> (forall(z, in(z, y) ==> in(z, x)))) /\ ((forall(z, in(z, y) ==> in(z, x))) ==> subset(y, x))
              )

        have(prem |- excess)  by RightAnd(
                Seq(
                  subset(x, y) /\ subset(y, x)
              , (
                (subset(x, y) ==> (forall(z, in(z, x) ==> in(z, y)))) /\ ((forall(z, in(z, x) ==> in(z, y))) ==> subset(x, y))
              )
              , (
                (subset(y, x) ==> (forall(z, in(z, y) ==> in(z, x)))) /\ ((forall(z, in(z, y) ==> in(z, x))) ==> subset(y, x))
              )
                )
        )(hypo, subx, suby)

        andThen((prem |- excess /\ forall(z, in(z, x) ==> in(z, y)) /\ forall(z, in(z, x) ==> in(z, y)))) by Rewrite

        showCurrentProof()

      }
      show
    }

    Ex.main(Array(""))
  }

  /**
   * An example of how to use the simple propositional solver.
   * The solver is complete (for propositional logic) but naive and won't succede on large formulas.
   */
  def solverExample(): Unit = {
    println("\n   --- Pierce's Law ---")
    checkProof(solveSequent(emptySeq +> ((A ==> B) ==> A ==> A)))
    println("\n   --- Various Tautologies ---")
    val tests: List[Sequent] = List(
      () |- Q \/ !Q,
      Q /\ !Q |- (),
      A /\ B |- A,
      A /\ B |- Set(B, Q),
      A |- A \/ B,
      Set(A, Q) |- A \/ B,
      () |- (A /\ B) ==> (A \/ C),
      Set(A, B) |- (A \/ C) /\ B,
      () |- ((T ==> Q) /\ (R ==> S)) ==> ((T \/ R) ==> (Q \/ S)),
      (T ==> Q) /\ (R ==> S) /\ (!Q \/ !S) |- !T \/ !R,
      () |- ((T /\ Q) \/ (!T /\ R)) <=> ((T ==> Q) /\ (!T ==> R))
    )
    println("\n   --- Wrong ---")
    tests
      .map(solveSequent)
      .zipWithIndex
      .foreach(p => {
        println(s"\nPropositional statement no ${p._2}")
        checkProof(p._1)
      })
  }

  /**
   * An example about how to use the tptp parser. Please note that only problems and formulas expressed in the
   * fof or cnf language of tptp are supported.
   */
  def tptpExample(): Unit = {
    val axioms = List(
      "( ~ ( ? [X] : ( big_s(X) & big_q(X) ) ) )",
      "( ! [X] : ( big_p(X) => ( big_q(X) | big_r(X) ) ) )",
      "( ~ ( ? [X] : big_p(X) ) => ? [Y] : big_q(Y) )",
      "( ! [X] : ( ( big_q(X) | big_r(X) ) => big_s(X) ) )"
    )
    val conjecture = "( ? [X] : ( big_p(X) & big_r(X) ) )"
    val anStatements = List(
      "fof(pel24_1,axiom,\n    ( ~ ( ? [X] :\n            ( big_s(X)\n            & big_q(X) ) ) )).",
      "\nfof(pel24_2,axiom,\n    ( ! [X] :\n        ( big_p(X)\n       => ( big_q(X)\n          | big_r(X) ) ) )).",
      "fof(pel24_3,axiom,\n    ( ~ ( ? [X] : big_p(X) )\n   => ? [Y] : big_q(Y) )).",
      "fof(pel24_4,axiom,\n    ( ! [X] :\n        ( ( big_q(X)\n          | big_r(X) )\n       => big_s(X) ) )).",
      "fof(pel24,conjecture,\n    ( ? [X] :\n        ( big_p(X)\n        & big_r(X) ) ))."
    )

    println("\n---Individual Fetched Formulas---")
    axioms.foreach(a => println(prettyFormula(parseToKernel(a))))
    println(prettyFormula(parseToKernel(conjecture)))

    println("\n---Annotated Formulas---")
    anStatements.map(annotatedFormulaToKernel).foreach(printAnnotatedFormula)

    println("\n---Problems---")

    try {
      val probs = getPRPproblems
      probs.foreach(p => println("Problem: " + p.name + " (" + p.domain + ") --- " + p.file))

      println("Number of problems found with PRP spc: " + probs.size)

      if (probs.nonEmpty) {
        println(" - First problem as illustration:")
        val seq = problemToSequent(probs.head)
        printProblem(probs.head)
        println("\n---Sequent---")
        println(prettySequent(seq))
      }
    } catch {
      case error: NullPointerException => println("You can download the tptp library at http://www.tptp.org/ and put it in main/resources")
    }

  }

  // Utility
  def printAnnotatedFormula(a: AnnotatedFormula): Unit = {
    if (a.role == "axiom") println("Given " + a.name + ": " + prettyFormula(a.formula))
    else if (a.role == "conjecture") println("Prove " + a.name + ": " + prettyFormula(a.formula))
    else println(a.role + " " + a.name + ": " + prettyFormula(a.formula))
  }

  def printProblem(p: Problem): Unit = {
    println("Problem: " + p.name + " (" + p.domain + ") ---")
    println("Status: " + p.status)
    println("SPC: " + p.spc.mkString(", "))
    p.formulas.foreach(printAnnotatedFormula)
  }

  val P = SchematicPredicateLabel("P", 1)

  val Q = PredicateFormula(VariableFormulaLabel("Q"), Seq())
  val R = PredicateFormula(VariableFormulaLabel("R"), Seq())
  val S = PredicateFormula(VariableFormulaLabel("S"), Seq())
  val T = PredicateFormula(VariableFormulaLabel("T"), Seq())
  val A = PredicateFormula(VariableFormulaLabel("A"), Seq())
  val B = PredicateFormula(VariableFormulaLabel("B"), Seq())
  val C = PredicateFormula(VariableFormulaLabel("C"), Seq())
  val H = VariableFormulaLabel("H")
  val x = VariableLabel("x")
  val y = VariableLabel("y")
  val z = VariableLabel("z")
  val f = SchematicFunctionLabel("f", 1)

  def ???? : Formula = ???
  def ?????(args: Any*) = ???
}
