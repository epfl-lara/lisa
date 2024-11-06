object Lattices extends lisa.Main {

  val x = variable
  val P = predicate[1]
  val f = function[1]

  val fixedPointDoubleApplication = Theorem(
    ∀(x, P(x) ==> P(f(x))) |- P(x) ==> P(f(f(x)))
  ) {
    sorry
  }

  // We introduce the signature of lattices
  val <= = ConstantPredicateLabel.infix("<=", 2)
  addSymbol(<=)
  val u = ConstantFunctionLabel.infix("u", 2) // join (union for sets, disjunction in boolean algebras)
  addSymbol(u)
  val n = ConstantFunctionLabel.infix("n", 2) // meet (interestion for sets, conjunction in boolean algebras)
  addSymbol(n)

  // Enables infix notation
  extension (left: Term) {
    def <=(right: Term): Formula = Lattices.<=.applyUnsafe(Seq(left, right))
    infix def u(right: Term): Term = Lattices.u.applyUnsafe(Seq(left, right))
    infix def n(right: Term): Term = Lattices.n.applyUnsafe(Seq(left, right))
  }

  // We now states the axioms of lattices

  val y = variable
  val z = variable

  val reflexivity = Axiom(x <= x)
  val antisymmetry = Axiom(((x <= y) /\ (y <= x)) ==> (x === y))
  val transitivity = Axiom(((x <= y) /\ (y <= z)) ==> (x <= z))
  val lub = Axiom(((x <= z) /\ (y <= z)) <=> ((x u y) <= z))
  val glb = Axiom(((z <= x) /\ (z <= y)) <=> (z <= (x n y)))

  // Let's prove some properties !

  val joinLowerBound = Theorem((x <= (x u y)) /\ (y <= (x u y))) {
    have(thesis) by Tautology.from(lub of (z := (x u y)), reflexivity of (x := (x u y)))
  }

  val meetUpperBound = Theorem(((x n y) <= x) /\ ((x n y) <= y)) {
    sorry
  }
  val joinCommutative = Theorem((x u y) === (y u x)) {
    val s1 = have((x u y) <= (y u x)) by Tautology.from(lub of (z := (y u x)), joinLowerBound of (x := y, y := x))
    have(thesis) by Tautology.from(s1, s1 of (x := y, y := x), antisymmetry of (x := x u y, y := y u x))
  }

  val meetCommutative = Theorem((x n y) === (y n x)) {
    sorry
  }
  val joinAbsorption = Theorem((x <= y) |- (x u y) === y) {
    sorry
  }

  val meetAbsorption = Theorem((x <= y) |- (x n y) === x) {
    sorry
  }

  val joinAssociative = Theorem((x u (y u z)) === ((x u y) u z)) {
    sorry
  }

  // Tedious, isn't it
  // Can we automate this?
  // Yes, we can!

  import lisa.utils.prooflib.ProofTacticLib.ProofTactic
  import lisa.utils.prooflib.Library

  object Whitman extends ProofTactic {
    def solve(using lib: library.type, proof: lib.Proof)(goal: Sequent): proof.ProofTacticJudgement = {
      TacticSubproof { // Starting the proof of `goal`

        if goal.left.nonEmpty || goal.right.size != 1 then proof.InvalidProofTactic("Whitman can only be applied to solve goals of the form () |- s <= t")
        else
          goal.right.head match {
            case <=(left: Term, right: Term) => {
              // We have different cases to consider
              (left, right) match {
                // 1. left is a join. In that case, lub gives us the decomposition
                case (u(a: Term, b: Term), _) =>
                  ???

                // 2. right is a meet. In that case, glb gives us the decomposition
                case (_, n(a: Term, b: Term)) =>
                  val s1 = solve(left <= a)
                  val s2 = solve(left <= b)
                  if s1.isValid & s2.isValid then have(left <= right) by Tautology.from(glb of (x := a, y := b, z := left), have(s1), have(s2))
                  else return proof.InvalidProofTactic("The inequality is not true in general ")

                // 3. left is a meet, right is a join. In that case, we try all pairs.
                case (n(a: Term, b: Term), u(c: Term, d: Term)) =>
                  val result = LazyList(a, b)
                    .map { e => (e, solve(e <= right)) }
                    .find { _._2.isValid }
                    .map { case (e, step) =>
                      have(left <= right) by Tautology.from(
                        have(step),
                        meetUpperBound of (x := a, y := b),
                        transitivity of (x := left, y := e, z := right)
                      )
                    } orElse {
                    LazyList(c, d)
                      .map { e => (e, solve(left <= e)) }
                      .find { _._2.isValid }
                      .map { case (e, step) =>
                        have(left <= right) by Tautology.from(
                          have(step),
                          joinLowerBound of (x := c, y := d),
                          transitivity of (x := left, y := e, z := right)
                        )
                      }
                  }
                  if result.isEmpty then return proof.InvalidProofTactic("The inequality is not true in general 3")

                // 4. left is a meet, right is a variable or unknown term.
                case (n(a: Term, b: Term), _) =>
                  val result = LazyList(a, b)
                    .map { e => (e, solve(e <= right)) }
                    .find { _._2.isValid }
                    .map { case (e, step) =>
                      have(left <= right) by Tautology.from(
                        have(step),
                        meetUpperBound of (x := a, y := b),
                        transitivity of (x := left, y := e, z := right)
                      )
                    }
                  if result.isEmpty then return proof.InvalidProofTactic("The inequality is not true in general")

                // 5. left is a variable or unknown term, right is a join.
                case (_, u(c: Term, d: Term)) =>
                  val result = LazyList(c, d)
                    .map { e => (e, solve(left <= e)) }
                    .find { _._2.isValid }
                    .map { case (e, step) =>
                      have(left <= right) by Tautology.from(
                        have(step),
                        joinLowerBound of (x := c, y := d),
                        transitivity of (x := left, y := e, z := right)
                      )
                    }
                  if result.isEmpty then return proof.InvalidProofTactic("The inequality is not true in general")

                // 6. left and right are variables or unknown terms.
                case _ =>
                  if !(left == right) then return proof.InvalidProofTactic("The inequality is not true in general 6")
                  else have(left <= right) by Restate.from(reflexivity of (x := left))

              }
            }

            case ===(left: Term, right: Term) =>
              val s1 = solve(left <= right)
              val s2 = solve(right <= left)
              if !(s1.isValid && s2.isValid) then return proof.InvalidProofTactic("The equality is not true in general")
              else
                have(left === right) by Tautology.from(
                  have(s1),
                  have(s2),
                  antisymmetry of (x := left, y := right)
                )
            case _ => return proof.InvalidProofTactic("Whitman can only be applied to solve goals of the form () |- s <= t")
          }
      }
    }
  }

  // uncomment when the tactic is implemented

  /*
  val test1 = Theorem(x <= x) {
    have(thesis) by Whitman.solve
  }
  val test2 = Theorem(x <= (x u y)) {
    have(thesis) by Whitman.solve
  }
  val test3 = Theorem((y n x) <= x) {
    have(thesis) by Whitman.solve
  }
  val test4 = Theorem((x n y) <= (y u z)) {
    have(thesis) by Whitman.solve
  }
  val idempotence = Theorem((x u x) === x) {
    have(thesis) by Whitman.solve
  }
  val meetAssociative = Theorem((x n (y n z)) === ((x n y) n z)) {
    have(thesis) by Whitman.solve
  }
  val semiDistributivity = Theorem((x u (y n z)) <= ((x u y) n (x u z))) {
    have(thesis) by Whitman.solve
  }
   */

}
