object Lattices extends lisa.Main {
  
    
    // We introduce the signature of lattices
    val <= = ConstantPredicateLabel("<=", 2)
    addSymbol(<=)
    val u = ConstantFunctionLabel("u", 2) //join (union for sets, disjunction in boolean algebras)
    addSymbol(u)
    val n = ConstantFunctionLabel("n", 2) //meet (interestion for sets, conjunction in boolean algebras)
    addSymbol(n)

    //Enables infix notation
    extension (left: Term) {
        def <=(right : Term):Formula = Lattices.<=.apply(left, right)
        def u(right : Term):Term = Lattices.u.apply(left, right)
        def n(right : Term):Term = Lattices.n.apply(left, right)
    }


    // We now states the axioms of lattices

    val x = variable
    val y = variable
    val z = variable

    val reflexivity  = Axiom(x <= x)
    val antisymmetry = Axiom(((x <= y) /\ (y <= x)) ==> (x === y))
    val transitivity = Axiom(((x <= y) /\ (y <= z)) ==> (x <= z))
    val lub = Axiom(((x <= z) /\ (y <= z)) <=> ((x u y) <= z))
    val glb = Axiom(((z <= x) /\ (z <= y)) <=> (z <= (x n y)))



    //Let's prove some properties !

    val joinLowerBound = Theorem((x <= (x u y)) /\ (y <= (x u y))) {
        have (thesis) by Tautology.from(lub of (z:= (x u y)), reflexivity of (x := (x u y)))
    }

    val joinCommutative = Theorem((x u y) === (y u x)) {
        val s1 = have((x u y) <= (y u x)) by Tautology.from(lub of (z := (y u x)), joinLowerBound of (x := y, y := x))
        have(thesis) by Tautology.from(s1, s1 of (x := y, y := x), antisymmetry of (x := x u y, y := y u x))
    }

    val joinAbsorption = Theorem((x <= y) |- (x u y) === y) {

    }

    val meetUpperBound = Theorem(((x n y) <= x) /\ ((x n y) <= y)) {
        have (thesis) by Tautology.from(glb of (z:= (x n y)), reflexivity of (x := (x n y)))
    }

    val meetCommutative = Theorem((x n y) === (y n x)) {
        val s1 = have((x n y) <= (y n x)) by Tautology.from(meetUpperBound, glb of (z := (y n x), x := y, y := x))
        have(thesis) by Tautology.from(s1, s1 of (x := y, y := x), antisymmetry of (x := x n y, y := y n x))
    }

    val meetAbsorption = Theorem((x <= y) |- (x n y) === x) {
        assume(x <= y)
        val s1 = have(x <= (x n y)) by Tautology.from(reflexivity, glb of (z := (x n y)))
        val s2 = have((x n y) <= x) by Tautology.from(meetUpperBound)
    }


    val joinAssociative = Theorem((x u (y u z)) === ((x u y) u z)) {
        sorry //TODO
    }


 
}
