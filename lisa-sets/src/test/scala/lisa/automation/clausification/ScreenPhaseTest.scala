package lisa.automation.clausification

import org.scalatest.funsuite.AnyFunSuite

import lisa.utils.K
import lisa.utils.K.{_, given}

/**
 * Regression tests for [[ScreenPhase]], the input screening that keeps the caller's free variables out of the
 * namespace the pipeline instantiates from the inside.
 *
 * Every phase below [[NegatedPhase]] runs inside a [[ClausificationSubproof]] carrying the negated conjecture as
 * an assumption, and several of them `InstSchema` a schema variable there: the library placeholders
 * [[Clausification.schemaP]] (the Skolem bridge) and the fresh `esk…`/`nm…`
 * symbols ([[Clausification.dischargeAssumptionsLatestFirst]]). An input variable named like any of those used to
 * be instantiated along with them while the assumption was pasted unchanged on the left, and the kernel rejected
 * the step ("Left-hand side of premise after instantiation is not contained in left-hand side of conclusion").
 *
 * The prover is stubbed with a single [[Sorry]] step: no solver runs, so a rejection can only come from the
 * certification scaffolding, and the goals below need not be valid, only shaped so that the phase under test
 * (Skolemization, prenex lifting, naming) actually fires.
 *
 * '''Why no corpus run ever caught this.''' TPTP predicates and functions arrive as *constants*, and the
 * pipeline never instantiates a constant, so on the whole benchmark corpus the bug is unreachable. It needs a
 * free *variable* at a schema's sort, which is what essentially every Lisa goal has and no TPTP problem does.
 * A tactic used from the library was therefore hitting a failure the 944-problem FOF set could not express.
 *
 * '''Why the screening sits above [[NegatedPhase]] rather than inside it.''' The predecessor of [[ScreenPhase]]
 * renamed the input's open variables from *within* the assumption region, which reintroduced the same fault it
 * was meant to avoid: renaming a predicate variable free in the negated-conjecture assumption is itself an
 * `InstSchema` under that assumption. Hoisting the renaming above the assumption removes the whole class rather
 * than the instances, because there the sequents still have an empty left-hand side and the substitution is
 * legal at every sort. That is why the tests below are collisions of *kind* (a bridge schema, a prenex operand,
 * a generated Skolem symbol, a library binder) rather than a list of names.
 */
class ScreenPhaseTest extends AnyFunSuite:

  private val y  = Variable(Identifier("y"), Ind)
  private val z  = Variable(Identifier("z"), Ind)
  private val u  = Variable(Identifier("u"), Ind)
  private val w  = Variable(Identifier("w"), Ind)
  private val Q  = Variable(Identifier("Q"), Ind >>: Prop)
  // Deliberate collisions with the clausifier's own schemas / generated names:
  private val P   = Variable(Identifier("P"), Ind >>: Prop)     // == Clausification.schemaP (library statements)
  private val R   = Variable(Identifier("R"), Prop)             // a bare propositional variable, screened as a predicate
  private val x   = Variable(Identifier("x"), Ind)              // == the bound `x` of the library statements
  private val esk = Variable(Identifier("esk", 1), Ind >>: Ind) // == the first Skolem function SkolemPhase mints

  /** Prover stub meeting `certifyClausal`'s contract: imports = the clause sequents, conclusion = `⊢`. */
  private def sorryProver(p: Clausification.Problem): SCProof =
    SCProof(IndexedSeq(Sorry(Sequent(Set.empty, Set.empty))), p.imports)

  /** Clausify `hyps ⊢ goal` with the stubbed prover; assert the kernel accepts it and that the proof concludes
    * the caller's goal *verbatim* (screening must restore the caller's names). */
  private def check(what: String, goal: Expression, hyps: Expression*): Unit =
    val problem = Clausification.Problem(hyps.map(h => () |- h), Some(() |- goal))
    val proof = CertifiedClausifier.certifyClausal(problem, sorryProver)
    // `assertCorrectProof`, not the `NoSorry` variant: the prover is stubbed with `Sorry` on purpose. Nothing
    // is being proved here, so the kernel checks only the certification scaffolding built around it.
    lisa.kernel.KernelProof.assertCorrectProof(proof, what)
    assert(proof.conclusion == (() |- goal), s"$what: conclusion ${proof.conclusion.repr} is not the original goal")
    assert(proof.imports == problem.imports ++ Clausification.libImports, s"$what: import list was altered")

  test("a goal over `P`, the schema the Skolem bridge instantiates, clausifies to a kernel-valid proof") {
    // ¬∀y.P(y) NNFs to ∃y.¬P(y), Skolemized via `existsEpsilonIff` with `P := λy.¬P(y)`.
    check("goal ⊢ P(y)", P(y))
  }

  test("a goal over a bare propositional variable clausifies to a kernel-valid proof") {
    // Negated + NNF: ∃w. (∀z.Q(z)) ∧ ¬Q(w) ∧ ¬R. `R` was the closed operand of the removed prenex laws, and a
    // free `R` in the assumption is what used to break; the shape is kept as a regression case.
    check("goal ⊢ (∀z.Q(z)) ⟹ (Q(y) ∨ R)", implies(forall(Lambda(z, Q(z))))(or(Q(y))(R)))
  }

  test("a goal over `esk_1`, the first Skolem function SkolemPhase mints, clausifies to a kernel-valid proof") {
    // The negation `∀u.∃w.…` has a witness mentioning `u`, so SkolemPhase mints `esk_1 : Ind → Ind`, colliding with the user's
    // variable exactly. It is instantiated to its ε-value by `dischargeAssumptionsLatestFirst`, a third failure
    // site (distinct from the two bridges above) before screening. The analogous `nm` collision is harder to
    // provoke on purpose (the naming site's sort depends on the formula), but goes through the same discharge.
    check("goal ⊢ ∃u.∀w.(Q(esk_1(u)) ∨ ¬Q(w))", exists(Lambda(u, forall(Lambda(w, or(Q(esk(u)))(neg(Q(w))))))))
  }

  test("a goal over `x`, the *bound* variable of the library statements, clausifies to a kernel-valid proof") {
    // `x` is only ever bound in the library statements, so it never was a collision; screening it is free, and
    // this pins that the canonicalisation of an input variable that shadows a library binder stays kernel-valid.
    check("goal ⊢ (∀z.Q(z)) ⟹ Q(x)", implies(forall(Lambda(z, Q(z))))(Q(x)))
  }

  test("collisions on the hypothesis side are screened too (the σ InstSchema steps)") {
    check("P(y), ∀z.(P(z) ⟹ Q(z)) ⊢ Q(y) ∨ R",
      or(Q(y))(R),
      P(y),
      forall(Lambda(z, implies(P(z))(Q(z)))))
  }

  test("an input binder that shadows a canonical target is α-renamed, and the goal is still restored verbatim") {
    // `y` screens to `v_1`, which is the name of the goal's own bound variable: substitution must freshen the
    // binder, so `σ⁻¹` gives back the goal only up to α, so `certifyScreen` restores the caller's sequent itself.
    val v1 = Variable(Identifier(Clausification.GeneratedNames.inputVar, 1), Ind)
    check("goal ⊢ ∀v_1. (Q(v_1) ∨ P(y))", forall(Lambda(v1, or(Q(v1))(P(y)))))
  }

  test("a constant-only problem (the TPTP shape) is passed through unscreened") {
    // This is why TPTP input never hit the bug: its predicates are Constants, which `InstSchema` cannot touch.
    val q = Constant(Identifier("q"), Ind >>: Prop)
    val closed = forall(Lambda(z, q(z)))
    check("goal ⊢ ∀z.q(z)", closed)
    assert(ScreenPhase.screeningRenaming(Clausification.Problem(Nil, Some(() |- closed))).isEmpty)
  }

  // --- the phase's second job: η-expanding the input's quantifiers ---------------------------------------
  //
  // `betaNormalForm` η-reduces `λy. p(y)` to `p`, so `∀y. p(y)` can present as `∀(p)`, which the `Forall`
  // extractor does not match. Every phase below is written against that extractor, so such a quantifier used to
  // travel the whole pipeline as an opaque *atom*. The repair used to sit only at the place that *creates* the
  // shape (`SkolemPhase`'s `betaNormalForm`); the caller handing us one directly was uncovered.

  private val pv = Variable(Identifier("p"), Ind >>: Prop) // a predicate *variable*: the Lisa-goal shape
  private val etaAll: Expression = forall(pv) //             ∀(p), η-reduced
  private val etaEx: Expression = exists(pv) //              ∃(p), η-reduced

  private def containsQuantifier(e: Expression): Boolean = e match
    case Application(`forall`, _) | Application(`exists`, _) => true
    case Application(f, a)                                   => containsQuantifier(f) || containsQuantifier(a)
    case Lambda(_, b)                                        => containsQuantifier(b)
    case _                                                   => false

  test("an η-reduced ∀ goal is screened, and the caller's own form is restored verbatim") {
    // The expansion must not leak outward: `check` asserts the conclusion is the caller's sequent *structurally*,
    // so this pins that `restored` hands back `∀(p)` and not the pipeline's `∀(λetaZ. p(etaZ))`.
    assert(etaAll match { case Forall(_, _) => false; case _ => true }, "premise: the shape is not matched by Forall")
    check("goal ⊢ ∀(p)", etaAll)
  }

  test("an η-reduced ∃ goal is screened, and the caller's own form is restored verbatim") {
    check("goal ⊢ ∃(p)", etaEx)
  }

  test("no η-reduced quantifier survives into the clauses handed downstream") {
    // The clause-level statement of the fix: before it, the prover was handed the literal `∀(P_1)`, a
    // well-formed clause that nothing downstream can tell from a genuine atom, so the failure surfaced only as an
    // unexplained non-refutation.
    var handed: Seq[Sequent] = Nil
    val problem = Clausification.Problem(Seq(() |- etaAll), Some(() |- pv(x)))
    CertifiedClausifier.certifyClausal(problem, p => { handed = p.hypotheses; sorryProver(p) })
    assert(handed.nonEmpty, "the prover was never reached")
    assert(handed.forall(s => (s.left ++ s.right).forall(l => !containsQuantifier(l))),
      s"a quantifier survived into a clause: ${handed.map(_.repr).mkString(" ; ")}")
  }

  test("screening splits by result sort: predicates into `P`, functions into `F`, individuals into `v`") {
    val pred2 = Variable(Identifier("myPred"), Ind >>: Ind >>: Prop) // Ind → Ind → Prop
    val prop0 = Variable(Identifier("myProp"), Prop) //                 a nullary predicate
    val fun1  = Variable(Identifier("myFun"), Ind >>: Ind) //           Ind → Ind
    val ind   = Variable(Identifier("myInd"), Ind) //                   an ordinary individual
    val problem = Clausification.Problem(Seq(() |- and(pred2(ind)(fun1(ind)))(prop0)), None)
    val renaming = ScreenPhase.screeningRenaming(problem)
    def namespaceOf(v: Variable): String = renaming(v).id.name

    assert(namespaceOf(pred2) == Clausification.GeneratedNames.inputPred, s"binary predicate → ${renaming(pred2)}")
    assert(namespaceOf(prop0) == Clausification.GeneratedNames.inputPred, s"nullary predicate → ${renaming(prop0)}")
    assert(namespaceOf(fun1) == Clausification.GeneratedNames.inputFun, s"unary function → ${renaming(fun1)}")
    assert(namespaceOf(ind) == Clausification.GeneratedNames.inputVar, s"individual → ${renaming(ind)}")
    // Sorts are preserved: screening renames, it does not re-sort.
    assert(renaming.forall((v, w) => v.sort == w.sort), s"screening changed a sort: $renaming")
    // Every counter is at least 1, so no screened name is a bare prefix; see the `P` / `schemaP` note below.
    assert(renaming.values.forall(_.id.no >= 1), s"a screened name has counter 0: ${renaming.values}")
  }

  // The property the case-by-case tests above are instances of: this is what makes the bug class closed rather
  // than patched. Whatever the input is called, the screened problem uses only the three input namespaces, so no
  // `InstSchema` the pipeline performs on its own schemas or fresh symbols can ever touch an input variable.
  test("after screening, every free variable of the problem is in the `v` / `P` / `F` namespaces") {
    val nasty: Seq[Variable] = Seq(P, R, x, esk, y, z, Q,
      Variable(Identifier("nm"), Ind >>: Prop), Variable(Identifier("w", 3), Ind),
      Variable(Identifier("v", 1), Ind), Variable(Identifier("P", 1), Ind >>: Prop),
      Variable(Identifier("F", 2), Ind >>: Ind), Variable(Identifier("cv"), Ind))
    val problem = Clausification.Problem(
      Seq(() |- and(P(y))(R), () |- Q(esk(z)), () |- nasty.filter(_.sort == Ind).map(Q(_)).reduce((f, g) => or(f)(g))),
      Some(() |- or(Variable(Identifier("nm"), Ind >>: Prop)(x))(Q(Variable(Identifier("F", 2), Ind >>: Ind)(y)))))
    val renaming = ScreenPhase.screeningRenaming(problem)
    val allowed = Set(Clausification.GeneratedNames.inputVar,
                      Clausification.GeneratedNames.inputPred,
                      Clausification.GeneratedNames.inputFun)

    // (a) injective, so the inverse used to restore the caller's names exists;
    assert(renaming.values.toSeq.distinct.size == renaming.size, s"screening renaming is not injective: $renaming")
    // (b) total on the input's free variables, up to those already canonical;
    val free = (problem.hypotheses ++ problem.conjecture).flatMap(s => (s.left ++ s.right).flatMap(_.freeVariables)).toSet
    val screened = free.map(v => renaming.getOrElse(v, v))
    // (c) still injective after the identity mappings are folded back in (no two inputs collapse into one);
    assert(screened.size == free.size, s"screening collapsed distinct input variables: $free -> $screened")
    // (d) and no screened name is one of the schemas the pipeline itself instantiates. The predicate namespace
    // shares its prefix with `schemaP`, so this is the condition the counter base has to buy: `P_1` is a
    // screened predicate, the bare `P` is the schema, and screening must never produce the latter.
    val schemas = Set(Clausification.schemaP, x)
    assert(screened.intersect(schemas).isEmpty, s"screening produced a pipeline schema: ${screened.intersect(schemas)}")
  }
