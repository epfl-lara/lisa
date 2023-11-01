
import lisa.prooflib.Substitution.ApplyRules as Substitution
import lisa.automation.Tableau
import scala.util.Try

object Lab05 extends lisa.Main {

    val x = variable
    val y = variable
    val z = variable

    // We introduce the signature of lattices
    val <= = ConstantPredicateLabel("<=", 2)
    addSymbol(<=)
    val u = ConstantFunctionLabel("u", 2) //join (union for sets, disjunction in boolean algebras)
    addSymbol(u)
    val n = ConstantFunctionLabel("n", 2) //meet (interestion for sets, conjunction in boolean algebras)
    addSymbol(n)

    //Enables infix notation
    extension (left: Term) {
        def <=(right : Term):Formula = Lab05.<=(left, right)
        def u(right : Term):Term = Lab05.u(left, right)
        def n(right : Term):Term = Lab05.n(left, right)
    }

    // We will now prove some statement about partial orders, which we axiomatize

    val reflexivity  = Axiom("reflexivity", x <= x)
    val antisymmetry = Axiom("antisymmetry", ((x <= y) /\ (y <= x)) ==> (x === y))
    val transitivity = Axiom("transitivity", ((x <= y) /\ (y <= z)) ==> (x <= z))
    val lub = Axiom("lub", ((x <= z) /\ (y <= z)) <=> ((x u y) <= z))
    val glb = Axiom("glb", ((z <= x) /\ (z <= y)) <=> (z <= (x n y)))

    //Now we'll need to reason with equality. We can do so with the Substitution tactic, which substitutes equals for equals.
    //The argument of Substitutions can be either an equality (s===t). In this case, the result should contain (s===t) in assumptions.
    //Or it can be a previously proven step showing a formula of the form (s===t). In this case, (s===t) does not
    //need to be in the left side of the conclusion, but assumptions of this precedently proven fact do.

    //Note however that Restate and Tautology now by themselves that t === t, for any t.


    val joinLowerBound = Theorem((x <= (x u y)) /\ (y <= (x u y))) {
        have (thesis) by Tautology.from(lub of (z:= (x u y)), reflexivity of (x := (x u y)))
    }


    val joinCommutative = Theorem((x u y) === (y u x)) {
        val s1 = have ((x u y) <= (y u x)) by Tautology.from(lub of (z := (y u x)), joinLowerBound of (x := y, y := x))
        have (thesis) by Tautology.from(s1, s1 of (x:=y, y:=x), antisymmetry of (x := x u y, y := y u x))
    }

    val joinAbsorption = Theorem((x <= y) |- (x u y) === y) {
        sorry //TODO
    }

    val meetUpperBound = Theorem(((x n y) <= x) /\ ((x n y) <= y)) {
        sorry //TODO
    }

    val meetCommutative = Theorem((x n y) === (y n x)) {
        sorry //TODO
    }

    val meetAbsorption = Theorem((x <= y) |- (x n y) === x) {
        sorry //TODO
    }


    val joinAssociative = Theorem((x u (y u z)) === ((x u y) u z)) {
        sorry //TODO
    }

    //Tedious, isn't it
    //Can we automate this?
    //Yes, we can!


    import lisa.prooflib.ProofTacticLib.ProofTactic
    import lisa.prooflib.Library

    object Whitman extends ProofTactic {
        def solve(using lib: library.type, proof: lib.Proof)(goal: Sequent): proof.ProofTacticJudgement = {
            if goal.left.nonEmpty || goal.right.size!=1 then
                proof.InvalidProofTactic("Whitman can only be applied to solve goals of the form () |- s <= t")
            else TacticSubproof {  //Starting the proof of `goal`

                goal.right.head match {
                    case <=(Seq(left: Term, right: Term)) => {
                        //We have different cases to consider
                        (left, right) match {
                            //1. left is a join. In that case, lub gives us the decomposition
                            case (u(Seq(a: Term, b: Term)), _) => 
                                //solve recursively a <= right and b <= right
                                val s1 = solve(a <= right)
                                val s2 = solve(b <= right)
                                //check if the recursive calls succedded
                                if s1.isValid & s2.isValid then
                                    have (left <= right) by Tautology.from(lub of (x := a, y := b, z:= right), have(s1), have(s2))
                                else fail("The inequality is not true in general")

                            //2. right is a meet. In that case, glb gives us the decomposition
                            case (_, n(Seq(a: Term, b: Term))) => 
                                ??? //TODO
                                
                            //3. left is a meet, right is a join. In that case, we try all pairs.
                            case (n(Seq(a: Term, b: Term)), u(Seq(c: Term, d: Term))) => 
                                ??? //TODO
                            

                            //4. left is a meet, right is a variable or unknown term.
                            case (n(Seq(a: Term, b: Term)), _) =>
                                //We try to find a proof for either a <= right or b <= right
                                LazyList(a, b).map{
                                    e => (e, solve(e <= right))
                                }.find{
                                    _._2.isValid
                                }.map{
                                    case (e, step) => 
                                        have(left <= right) by Tautology.from(
                                            have(step),
                                            meetUpperBound of (x:=a, y:=b),
                                            transitivity of (x := left, y := e, z:=right)
                                        )
                                    
                                }.getOrElse(fail("The inequality is not true in general"))


                            //5. left is a variable or unknown term, right is a join.
                            case (_, u(Seq(c: Term, d: Term))) =>
                                ??? //TODO


                            //6. left and right are variables or unknown terms.
                            case _ =>
                                ??? //TODO
                        }
                    }

                    case ===(Seq(left: Term, right: Term)) => 
                        ???
                    case _ => fail("Whitman can only be applied to solve goals of the form () |- s <= t or () |- s === t")
                }
            }
            
        }

    }


    //uncomment when the tactic is implemented

    val test1 = Theorem(x <= x) {
        sorry //have(thesis) by Whitman.solve
    }
    val test2 = Theorem(x <= (x u y)) {
        sorry //have(thesis) by Whitman.solve
    }
    val test3 = Theorem((y n x) <= x) {
        sorry //have(thesis) by Whitman.solve
    }
    val test4 = Theorem((x n y) <= (y u z)) {
        sorry //have(thesis) by Whitman.solve
    }
    val idempotence = Theorem((x u x) === x) {
        sorry //have(thesis) by Whitman.solve
    }
    val meetAssociative = Theorem((x n (y n z)) === ((x n y) n z)) {
        sorry //have(thesis) by Whitman.solve
    }
    val semiDistributivITY = Theorem((x u (y n z)) <= ((x u y) n (x u z))) {
        sorry //have(thesis) by Whitman.solve
    }




}
