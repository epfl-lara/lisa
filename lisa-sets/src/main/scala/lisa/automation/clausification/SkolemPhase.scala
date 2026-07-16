package lisa.automation.clausification

import lisa.utils.K.{_, given}
import Clausification.*

private[clausification] object SkolemPhase:

  def certifySkolem(problem: Problem, prover: ClausificationProver): ClausificationProof =
    certifyAxiomwise(problem, prover, (ax, counter, ctx) => {
      val phi = singleRightFormula(ax, "axiom")
      skolemizeOne(phi, counter).map { case SkolemStep(skoFormula, bridge) =>
        // Outer steps:
        //   step 0: bridge proof, concluding `phi ⊢ skoFormula`. The bridge takes
        //           [[existsEpsilonIffStatement]] as a single import, supplied here
        //           via [[libIffRef]] into the outer library imports.
        //   step 1: Cut against ax, concluding `() ⊢ skoFormula`.
        val skoaxF     = () |- skoFormula
        val bridgeStep = KernelStep(SCSubproof(bridge, IndexedSeq(libIffRef(ctx.nonLibSize))))
        val cutStep    = KernelStep(Cut(skoaxF, -1, 0, phi))
        (skoaxF, IndexedSeq(bridgeStep, cutStep), 1)
      }
    })

  /**
    * Result of one Skolemization step on a formula.
    *
    *   - `skoFormula`     : the original formula with the leftmost outermost existential
    *                        `∃x. φ(x)` (possibly nested under `∀`/`∧`/`∨`) replaced by
    *                        `φ[ε(λx.φ)/x]` — i.e. the bound variable substituted by the
    *                        Hilbert-epsilon witness directly. This is the formula the
    *                        parent recursion threads as the new axiom; no further
    *                        substitution across the recursive proof is needed.
    *   - `bridge`         : a closed (no-imports modulo [[existsEpsilonIffStatement]])
    *                        SC proof concluding `f ⊢ skoFormula`. This is what the
    *                        parent uses to derive `() ⊢ skoFormula` from `() ⊢ f` via
    *                        a single Cut.
    */
  case class SkolemStep(
      skoFormula: Expression,
      bridge: SCProof
  )

  /**
    * Single-step Skolemization with bridge proof.
    *
    * Pops the leftmost outermost existential `∃x. φ` reachable through `∀`/`∧`/`∨`
    * and replaces it directly by `φ[ε(λx. φ)/x]` (the Hilbert-epsilon witness form).
    * Synthesises a closed SC proof bridging the original formula `f` to its
    * post-substitution form in a constant number of steps, by:
    *
    *   1. Instantiating [[Quantifiers.existsEpsilonIff]] (the schematic equivalence
    *      `(∃x. P(x)) ⇔ P(εx. P(x))`) at `P := λx. φ` to obtain the local equivalence
    *      `(∃x. φ) ⇔ φ[ε(λx.φ)/x]`.
    *   2. Using one [[RightSubstIff]] application to lift that local equivalence into
    *      the position chosen inside `f` (via a context `λp. phi_body`, where
    *      `phi_body` is `f` with the chosen `∃x.φ` replaced by a fresh propositional
    *      variable `p`).
    *
    * Returns `None` if `f` contains no existential under the supported connectives.
    */
  def skolemizeOne(f: Expression, counter: Counter): Option[SkolemStep] = {
    checkInterrupted()
    // Single descent that builds:
    //   - phi_body  : f with the leftmost ∃x.φ replaced by `p(b_1)…(b_k)`, where
    //                 `b_1…b_k` are the enclosing universally-bound variables on
    //                 the path to the ∃ and `p` is a fresh higher-sort marker
    //                 (sort `s_1 → … → s_k → Prop`). Used as the body of the
    //                 RightSubstIff context. Parameterising the marker by the
    //                 enclosing binders is essential: without it, capture-avoiding
    //                 substitution α-renames the surrounding ∀-binders and strands
    //                 their occurrences inside the substituted ε-form (see the
    //                 Skolem bridge below).
    //   - x, inner  : the bound variable and body of the chosen ∃, used to
    //                 instantiate the schematic [[existsEpsilonIffStatement]] at
    //                 `P := λx.inner[b_i := u_i]` for fresh witnesses `u_i`.
    //   - p         : the fresh marker variable used as the substitution point.
    //   - enclosing : enclosing universal binders, outermost first.
    case class Hit(
        phi_body: Expression,
        x: Variable,
        inner: Expression,
        p: Variable,
        enclosing: Seq[Variable]
    )

    def descend(e: Expression, enclosing: Seq[Variable]): Option[Hit] =
      def bin(g: Expression, h0: Expression, op: (Expression, Expression) => Expression): Option[Hit] =
        descend(g, enclosing).map(h => h.copy(phi_body = op(h.phi_body, h0)))
          .orElse(descend(h0, enclosing).map(h => h.copy(phi_body = op(g, h.phi_body))))
      e match
        case Exists(x, inner) =>
          val pSort = enclosing.foldRight(Prop: Sort)((b, acc) => b.sort >>: acc)
          val p     = Variable(Identifier(s"_p${counter.next()}", 0), pSort)
          val pApp  = enclosing.foldLeft(p: Expression)(_(_))
          Some(Hit(pApp, x, inner, p, enclosing))

        case Forall(y, body) =>
          descend(body, enclosing :+ y).map(h => h.copy(phi_body = forall(Lambda(y, h.phi_body))))

        case And(g, h0) => bin(g, h0, and(_)(_))
        case Or(g, h0)  => bin(g, h0, or(_)(_))

        // In NNF, `Neg` only wraps atoms, so no existential reaches this case.
        case _ => None

    descend(f, Seq.empty).map { h =>
      val k = h.enclosing.size

      // Pick fresh witnesses u_i (one per enclosing binder), all kept distinct from
      // every name occurring in `f`. They will play the role of the universally-
      // quantified arguments of the iff that bridges the substitution.
      val taken = scala.collection.mutable.Set.empty[Identifier] ++ f.freeVariables.map(_.id)
      val us = h.enclosing.map { b =>
        val id = freshId(taken, Identifier("u", 0))
        taken += id
        Variable(id, b.sort)
      }
      val renaming: Map[Variable, Expression] = h.enclosing.zip(us).toMap

      // The existential's own bound variable `x`. If it shares a name with an enclosing binder, the
      // `renaming` above (keyed on those binders) would ALSO rewrite `x`'s own bound occurrences inside
      // `h.inner` — because the two are the *same* [[Variable]] — desynchronising the reconstructed
      // RightSubstIff context from `f` and yielding a kernel-invalid certificate (e.g. `∀Y. ∃Y. p(Y)`,
      // or the LCL modal encodings that reuse quantifier names across nesting). α-rename `x` to a fresh
      // name disjoint from every enclosing binder (and every `u_i`, already in `taken`) first, so the
      // enclosing renaming cannot touch it. Only needed on an actual clash, so common proofs are unchanged.
      val (xVar, innerX) =
        if h.enclosing.contains(h.x) then
          val xf = Variable(freshId(taken ++ h.enclosing.iterator.map(_.id), h.x.id), h.x.sort)
          (xf, substituteVariablesOpti(h.inner, Map(h.x -> xf)))
        else (h.x, h.inner)

      // Local quantities, all in terms of the fresh u_i (and the freshened `xVar`):
      //   innerU    = inner[b_i := u_i][x := xVar]
      //   lambdaInnerU = λxVar. innerU
      //   targetU   = ∃xVar. innerU
      //   epsFormU  = innerU[xVar := ε(λxVar.innerU)]
      //   localIff  = targetU ⇔ epsFormU         (the existsEpsilonIff instance)
      val innerU       = substituteVariablesOpti(innerX, renaming)
      val lambdaInnerU = Lambda(xVar, innerU)
      val targetU      = exists(lambdaInnerU)
      val epsFormU     = substituteVariablesOpti(innerU, Map(xVar -> epsilon(lambdaInnerU)))
      val localIff     = targetU <=> epsFormU

      // The higher-sort substitution lambdas. After β, `targetLambda(u_1)…(u_k)`
      // is `targetU`, and similarly for `epsLambda`. The kernel checker for
      // [[RightSubstIff]] (= [[RightSubstEq]]) synthesises the universally-
      // quantified iff `∀x_no…x_{no+k-1}. targetLambda(...) ⇔ epsLambda(...)`,
      // which is α-equivalent (after β) to `outerIff` below.
      val targetLambda = us.foldRight(targetU: Expression)((u, e) => Lambda(u, e))
      val epsLambda    = us.foldRight(epsFormU: Expression)((u, e) => Lambda(u, e))
      val outerIff     = us.foldRight(localIff: Expression)((u, e) => forall(Lambda(u, e)))

      // Skolem result: substitute `p` with `epsLambda` in `phi_body`, then β-
      // normalise. β-normalisation is essential so that subsequent
      // [[skolemizeOne]] passes can syntactically descend through the result:
      // without it, the freshly-introduced `(λu_i.body)(b_i)` redexes hide
      // inner `Forall/Exists/And/Or` nodes from the descent matcher.
      //
      // `betaNormalForm` also η-reduces, so a quantifier body `λy. p(x, y)` collapses to `∀(p(x))`, which the
      // `Forall`/`Exists` extractors (they need an explicit `Lambda`) miss — stranding the quantifier as an
      // opaque atom in the clause. Re-expand it so prenex/Tseitin see the binder. (See [[etaExpandQuantifiers]].)
      val skoFormula =
        etaExpandQuantifiers(substituteVariablesOpti(h.phi_body, Map(h.p -> epsLambda)).betaNormalForm)

      // Bridge proof: takes [[existsEpsilonIffStatement]] as a single import,
      // conclusion `f ⊢ skoFormula`. Reuses [[Quantifiers.existsEpsilonIff]] to
      // avoid rebuilding the local iff proof at every Skolem site: instantiate
      // the schematic theorem to obtain `() ⊢ localIff`, wrap with `RightForall`
      // × k to lift it to `outerIff`, then lift it into context via RightSubstIff.
      val steps = scala.collection.mutable.ArrayBuffer.empty[SCProofStep]
      // 0: () ⊢ localIff   (single InstSchema of existsEpsilonIff)
      steps += InstSchema(() |- localIff, -1, Map(schemaP -> lambdaInnerU))
      // 1..k: RightForall × k (innermost first)
      var current: Expression = localIff
      var ref = 0
      for (i <- us.indices.reverse) {
        val u = us(i)
        val wrapped = forall(Lambda(u, current))
        steps += RightForall(() |- wrapped, ref, current, u)
        ref = steps.size - 1
        current = wrapped
      }
      val outerIffRef = ref
      // k+1: f ⊢ f
      steps += Hypothesis(f |- f, f)
      val hypRef = steps.size - 1
      // k+2: lift the local iff into context, replacing `p` with the substitution.
      steps += RightSubstIff(
        Sequent(Set(f, outerIff), Set(skoFormula)),
        hypRef,
        Seq((targetLambda, epsLambda)),
        (Seq(h.p), h.phi_body)
      )
      val substRef = steps.size - 1
      // k+3: discharge `outerIff` via Cut.
      steps += Cut(f |- skoFormula, outerIffRef, substRef, outerIff)

      // The recursion now sees the ε-form directly: no cross-proof substitution.
      SkolemStep(skoFormula, SCProof(steps.toIndexedSeq, IndexedSeq(existsEpsilonIffStatement)))
    }
  }
