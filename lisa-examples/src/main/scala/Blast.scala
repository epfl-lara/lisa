
import lisa.utils.K.{_, given}
import lisa.utils.K
import scala.collection.immutable.HashSet
import scala.collection.immutable.HashMap
import lisa.fol.FOL as F
import lisa.utils.parsing.FOLPrinter.prettyTerm
import lisa.utils.parsing.FOLPrinter.prettyFormula


/**
  * Now need to deal with variables unifying with terms containing themselves
  * Check if such substitution tests pass
  * Then, optimize unification check by not checking all pairs all the time
  * Then, prune branches that are not needed by detecting if a node is useful or not (backtracking to parent branch, proofs)
  * Then, shortcut branches by checking if they are OL-true or OL-false
  * 
  * Next test: No quantifiers but actual terms with variables
  */

object Blast {
    import BlastTest.{printif, doprint}

    case class Branch(
        beta: List[ConnectorFormula],  //label = Not(And(...))
        delta: List[BinderFormula],  //Exists(...))
        gamma: List[BinderFormula],  //Forall(...)
        atoms: (List[PredicateFormula], List[PredicateFormula]),    // split into positive and negatives!
        unifiable: Map[VariableLabel, BinderFormula], //map between metavariables and the original formula they came from
        triedInstantiation: Map[VariableLabel, Set[Term]], //map between metavariables and the term they were already instantiated with
        history: Formula, //the formula that was used to create this branch
        parent: Branch, //the parent branch
        maxIndex:Int
        //active: List[Formula], used: HashSet[Int], unifiable: HashSet[Identifier]
    ){
        def pop(f : Formula) : Branch = f match
            case f @ ConnectorFormula(Or, args) => 
                if (beta.nonEmpty && beta.head.uniqueNumber == f.uniqueNumber) copy(beta=beta.tail, history = beta.head) else throw Exception("First formula of beta is not f")
            case f @ BinderFormula(Exists, x, inner) => 
                if (delta.nonEmpty && delta.head.uniqueNumber == f.uniqueNumber) copy(delta=delta.tail, history = delta.head) else throw Exception("First formula of delta is not f")
            case f @ BinderFormula(Forall, x, inner) => 
                if (gamma.nonEmpty && gamma.head.uniqueNumber == f.uniqueNumber) copy(gamma=gamma.tail, history = gamma.head) else throw Exception("First formula of gamma is not f")
            case ConnectorFormula(And, args) => 
                throw Exception("Branches never contain alpha formulas")
            case f @ PredicateFormula(id, args) => 
                throw Exception("Should not pop Atoms")
            case f @ ConnectorFormula(Neg, List(PredicateFormula(id, args))) => 
                throw Exception("Should not pop Atoms")
            case _ => ???

        def prepended(f:Formula) : Branch = f match
            case ConnectorFormula(And, args) => this.prependedAll(args)
            case f @ ConnectorFormula(Or, args) => this.copy(beta = f :: beta)
            case f @ BinderFormula(Exists, x, inner) => this.copy(delta = f :: delta)
            case f @ BinderFormula(Forall, x, inner) => this.copy(gamma = f :: gamma)
            case f @ PredicateFormula(id, args) => 
                this.copy(atoms = (f :: atoms._1, atoms._2))
            case ConnectorFormula(Neg, List(f @ PredicateFormula(id, args))) => 
                this.copy(atoms = (atoms._1, f :: atoms._2))
            case _ => ???

        def prependedAll(l: Seq[Formula]) : Branch = l.foldLeft(this)((a, b) => a.prepended(b))

        import Branch.*
        override def toString(): String = 
            val pretUnif = unifiable.map((x, f) => x.id + " -> " + prettyFormula(f)).mkString("Unif(", ", ", ")")
            //val pretTried = triedInstantiation.map((x, t) => x.id + " -> " + prettyTerm(t, true)).mkString("Tried(", ", ", ")")
            val pretHistory = if history == null then "null" else prettyFormula(history)
            s"Branch(${prettyIte(beta, "beta")}, ${prettyIte(delta, "delta")}, ${prettyIte(gamma, "gamma")}, ${prettyIte(atoms._1, "+")}, ${prettyIte(atoms._2, "-")}, $pretUnif, _, $pretHistory, _)"
        
    }
    object Branch{
        def empty = Branch(Nil, Nil, Nil, (Nil, Nil), Map.empty, Map.empty, null, null, 1)
        def empty(n:Int) = Branch(Nil, Nil, Nil, (Nil, Nil), Map.empty, Map.empty, null, null, n)
        def prettyIte(l:Iterable[Formula], head:String):String = l match
            case Nil => "Nil"
            case _ => l.map(prettyFormula(_, true)).mkString(head+"(", ", ", ")")

    }

    def makeVariableNamesUnique(f:Formula, nextId:Int, seen:Set[VariableLabel]): (Formula, Int, Set[VariableLabel]) = f match
        case ConnectorFormula(label, args) => 
            val (nArgs, nnId, nSeen) = args.foldLeft((List(): Seq[Formula], nextId, seen))((prev, next) => 
                val (l, n, s) = prev
                val (nf, nn, ns) = makeVariableNamesUnique(next, n, s)
                (l :+ nf, nn, ns)
            )
            (ConnectorFormula(label, nArgs), nnId, nSeen)
        case pf: PredicateFormula => (pf, nextId, seen)
        case BinderFormula(label, x, inner) => 
            if (seen.contains(x))
                val (nInner, nnId, nSeen) = makeVariableNamesUnique(inner, nextId+1, seen)
                val newX = VariableLabel(Identifier(x.id, nextId))
                (BinderFormula(label, newX, substituteVariablesInFormula(nInner, Map(x -> newX), Seq())), nnId, nSeen)
            else
                val (nInner, nnId, nSeen) = makeVariableNamesUnique(inner, nextId, seen + x)
                (BinderFormula(label, x, nInner), nnId, nSeen)
    
    
    def solve(S:F.Sequent):Boolean = {
        val ks = S.underlying
        val f = K.ConnectorFormula(K.And, (ks.left.toSeq ++ ks.right.map(f => K.ConnectorFormula(K.Neg, List(f)))))
        val taken = f.schematicTermLabels
        val nextIdNow = if taken.isEmpty then 0 else taken.maxBy(_.id.no).id.no+1
        val (fnamed, nextId, _) = makeVariableNamesUnique(f, nextIdNow, f.freeVariables)
        val nf = reducedNNFForm(fnamed)
        printif("solve f     : " + prettyFormula(f))
        printif("solve fnames: " + prettyFormula(fnamed))
        printif("solve nf    : " + prettyFormula(nf))

        nf match
            case ConnectorFormula(And, args) => decide(Branch.empty(nextId).prependedAll(args), Nil)
            case _ => decide(Branch.empty.prepended(nf), Nil)
        
    }
    type Substitution = Map[VariableLabel, Term]
    val Substitution = HashMap

    /*
    def substitute(t:Term, s:Substitution):Term = t match
        case VariableTerm(x:VariableLabel) => if (s.contains(x)) s(x) else t
        case Term(id, args) => Term(id, args.map(substitute(_, s)))

        */

    def unify(t1:Term, t2:Term, current:Substitution, br: Branch):Option[Substitution] = (t1, t2) match
        case (VariableTerm(x), VariableTerm(y)) if br.unifiable.contains(x) && br.unifiable.contains(y)  => 
            if (x == y) Some(current) else Some(current + (x -> substituteVariablesInTerm(t2, current)))
        case (VariableTerm(x), t2:Term) if br.unifiable.contains(x) => 
            if t2.freeVariables.contains(x) then None 
            else if (current.contains(x)) unify(current(x), t2, current, br) else Some(current + (x -> substituteVariablesInTerm(t2, current)))
        case (t1:Term, VariableTerm(y)) if br.unifiable.contains(y) => 
            if t1.freeVariables.contains(y) then None 
            else if (current.contains(y)) unify(t1, current(y), current, br) else Some(current + (y -> substituteVariablesInTerm(t1, current)))
        case (Term(label1, args1), Term(label2, args2)) => 
            if label1 == label2 && args1.size == args2.size then
                args1.zip(args2).foldLeft(Some(current):Option[Substitution])((prev, next) => prev match
                    case None => None
                    case Some(s) => unify(next._1, next._2, s, br)
                )
            else None

    def unifyPred(pos: PredicateFormula, neg: PredicateFormula, br: Branch): Option[Substitution] = {
        (pos, neg) match
            case (PredicateFormula(id1, args1), PredicateFormula(id2, args2)) if (id1 == id2 && args1.size == args2.size) => 
                args1.zip(args2).foldLeft(Some(Substitution.empty): Option[Substitution])((prev, next) => prev match
                    case None => None
                    case Some(s) => unify(next._1, next._2, s, br)
                )
            case _ => None
        
    }

    //Find if a branch can be closed
    //If it can, return a list of substitutions that closes it
    //The list is empty if the branch cannot be closed
    //The substitution cannot do substitutions that were already done in triedInstantiation.
    def close(branch: Branch) : Option[Substitution] = {
        val pos = branch.atoms._1.iterator
        var substitutions: List[Substitution] = Nil

        while (pos.hasNext) {
            val p = pos.next()
            if (p.label == bot) return Some(Substitution.empty)
            val neg = branch.atoms._2.iterator
            while (neg.hasNext) {
                val n = neg.next()
                unifyPred(p, n, branch) match
                    case None => ()
                    case Some(unif) => substitutions = unif :: substitutions
            }
        }

        //printif("closing: " + substitutions)

        val cr = substitutions.filterNot(s => 
            s.exists((x, t) => 
                //printif("exists: " + (x, t))
                val v = branch.triedInstantiation.contains(x) && branch.triedInstantiation(x).contains(t)
                //if branch.triedInstantiation.contains(x) then printif("tried: " +  branch.triedInstantiation(x))
                //printif("v: " + v)
                v
            )
        )

        //printif("closing: " + cr)
        cr.sortBy(_.size).headOption
    }




    //Explodes one beta formula, and alpha-simplifies it
    //Add the exploded formula to the used list, if one beta formula is found
    //If the result is a singleton, then no beta branch was found and the formula it contains is exactly the input
    def beta(branch: Branch):List[Branch] = {
        if (branch.beta.isEmpty) List(branch)
        else
            val f = branch.beta.head
            val b1 = branch.pop(f)
            val resList = f.args.toList.map(disjunct => {
                    disjunct match {
                        case ConnectorFormula(And, args) => b1.prependedAll(args)
                        case d => b1.prepended(d)}
            })
            resList
    }

    //Find an existenially quantified variable
    //Add the unquantified formula to the branch
    //Since the bound variable is not marked as suitable for instantiation, it behaves as a constant symbol (skolem)
    def delta(branch: Branch):(Branch, Boolean) = {
        if (branch.delta.isEmpty) (branch, false)
        else
            val f = branch.delta.head
            val b1 = branch.pop(f)
            (b1.prepended(f.inner), true)
    }

    //Find a universally quantified variable
    //Add the unquantified formula to the branch and mark the bound variable as suitable for unification
    def gamma(branch: Branch):(Branch, Boolean) = {
        if (branch.gamma.isEmpty) (branch, false)
        else
            val f = branch.gamma.head
            branch.unifiable.get(f.bound) match
                case None => 
                    val b1 = branch.copy(gamma = branch.gamma.tail, unifiable = branch.unifiable + (f.bound -> f), history = branch.gamma.head)
                    (b1.prepended(f.inner), true)
                case Some(value) =>
                    val newBound = VariableLabel(Identifier(f.bound.id.name, branch.maxIndex))
                    val newInner = substituteVariablesInFormula(f.inner, Map(f.bound -> newBound), Seq())
                    val b1 = branch.copy(gamma = branch.gamma.tail, unifiable = branch.unifiable + (newBound -> f), history = branch.gamma.head, maxIndex = branch.maxIndex+1)
                    (b1.prepended(newInner), true)
    }

    // When a ground instantiation is found, apply it to the branch
    // The non-metavariable variant of the gama rule
    def applyInst(branch: Branch, x:VariableLabel, t:Term): Branch = {
        val f = branch.unifiable(x)
        val newTried = branch.triedInstantiation.get(x) match
            case None => branch.triedInstantiation + (x -> Set(t))
            case Some(s) => branch.triedInstantiation + (x -> (s + t))
        
        val r = branch.prepended(instantiate(f.inner, f.bound, t)).copy(history = f, triedInstantiation = newTried)
        r
    }


    def decide(branch: Branch, remainingBranches: List[Branch]): Boolean = {
        printif(branch)
        if (doprint) Thread.sleep(200)
        val closeSubst = close(branch)
        if (closeSubst.nonEmpty && closeSubst.get.isEmpty)                          //If branch can be closed without Instantiation (Hyp)
            if remainingBranches.isEmpty then true else
                decide(remainingBranches.head, remainingBranches.tail)
        else if (branch.delta.nonEmpty) decide(delta(branch)._1, remainingBranches) //If branch contains a Delta formula (LeftExists)
        else if (branch.beta.nonEmpty)                                              //If branch contains a Beta formula (LeftOr)
            val list = beta(branch)
            decide(list.head, remainingBranches.prependedAll(list.tail))
        else if (branch.gamma.nonEmpty) decide(gamma(branch)._1, remainingBranches) //If branch contains a Gamma formula (LeftForall)
        else if (closeSubst.nonEmpty && closeSubst.get.nonEmpty)                         //If branch can be closed with Instantiation (LeftForall)
            decide(applyInst(branch, closeSubst.get.head._1, closeSubst.get.head._2), remainingBranches)
        else false
        

    }





    def instantiate(f:Formula, x:VariableLabel, t:Term):Formula = f match
        case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(instantiate(_, x, t)))
        case PredicateFormula(id, args) => PredicateFormula(id, args.map(substituteVariablesInTerm(_, Substitution(x -> t))))
        case BinderFormula(label, y, inner) => if (x == y) f else BinderFormula(label, y, instantiate(inner, x, t))


}

object BlastTest extends lisa.Main {
    import Blast._

    val w = variable
    val x = variable
    val y = variable
    val z = variable

    val a = formulaVariable
    val b = formulaVariable
    val c = formulaVariable
    val d = formulaVariable
    val e = formulaVariable

    val f = function[1]
    val g = function[1]
    val h = function[2]

    val P = predicate[1]
    val Q = predicate[1]
    val R = predicate[2]

    var doprint:Boolean = false
    def printif(s:Any) = if doprint then println(s) else ()


    val posi = List(
        a <=> a,
        a \/ !a,
        ((a ==> b) /\ (b ==> c)) ==> (a ==> c),
        (a <=> b) <=> ((a/\b) \/ (!a /\ !b)),
        ((a ==> c) /\ (b ==> c)) <=> ((a \/ b) ==> c),
        ((a ==> b) /\ (c ==> d)) ==> ((a \/ c) ==> (b \/ d))
    ).zipWithIndex.map(f => (f._2, f._1, solve(() |- f._1)))
    println(s"Propositional Positive cases (${posi.size})")
    if posi.exists(f => !f._3) then 
        posi.foreach((i, f, b) => println(s"$i $b" + (if !b then s" $f" else "")))
    else println("All TRUE")


    val nega = List(
        !(a <=> a),
        !a \/ !a,
        !(((a ==> b) /\ (b ==> c)) ==> (a ==> c)),
        !((a <=> b) <=> ((a/\b) \/ (!a \/ !b))),
        !(((a ==> c) /\ (b ==> c)) <=> ((a \/ b) ==> c)),
        !(((a ==> b) /\ (c ==> d)) ==> ((a \/ c) ==> (b \/ d))),
        ((a ==> b) /\ (b ==> a)) ==> (a ==> c),
        (a <=> b) <=> ((a/\b) \/ (a /\ !b)),
        ((a ==> c) /\ (b ==> c)) <=> ((a \/ b) ==> a),
        ((a ==> b) /\ (c ==> d)) ==> ((a \/ c) ==> (b))
    ).zipWithIndex.map(f => (f._2, f._1, solve(() |- f._1)))
    println(s"Propositional Negative cases (${nega.size})")
    if nega.exists(f => f._3) then 
        nega.foreach((i, f, b) => println(s"$i $b" + (if b then s" $f" else "")))
    else println("All FALSE")


    // Quantifier Free

    val posqf = List(
        posi.map(fo => fo._2.substitute(a:= P(h(x, y)), b := P(x), c:= R(x, h(x, y))) ),
        posi.map(fo => fo._2.substitute(a:= P(h(x, y)), b := P(h(x, y)), c:= R(x, h(x, f(x)))) ),
        posi.map(fo => fo._2.substitute(a:= R(y, y), b := P(h(y, y)), c:= R(h(x, y), h(z, y))) ),
    ).flatten.zipWithIndex.map(f => (f._2, f._1, solve(() |- f._1)))
    println(s"First Order Quantifier Free Positive cases (${posqf.size})")
    if posqf.exists(f => !f._3) then 
        posqf.foreach((i, f, b) => println(s"$i $b" + (if !b then s" $f" else "")))
    else println("All TRUE")


    val negqf = List(
        nega.map(fo => fo._2.substitute(a:= P(h(x, y)), b := P(x), c:= R(x, h(x, y))) ),
        nega.map(fo => fo._2.substitute(a:= P(h(x, y)), b := P(h(x, z)), c:= R(x, h(x, x))) ),
        nega.map(fo => fo._2.substitute(a:= R(y, y), b := P(h(y, y)), c:= R(h(x, y), h(z, y))) ),
    ).flatten.zipWithIndex.map(f => (f._2, f._1, solve(() |- f._1)))
    println(s"First Order Quantifier Free Negative cases (${negqf.size})")
    if negqf.exists(f => f._3) then 
        negqf.foreach((i, f, b) => println(s"$i $b" + (if b then s" $f" else "")))
    else println("All FALSE")

    // First Order Easy


    val poseasy = List(
        posi.map(fo => fo._2.substitute(a:= forall(x, P(x)), b := forall(x, P(y)), c:= exists(x, P(x)) )),
        posi.map(fo => fo._2.substitute(a:= forall(x, P(x) /\ Q(f(x))), b := forall(x, P(x) \/ R(y, x)), c:= exists(x, Q(x) ==> R(x, y)) )),
        posi.map(fo => fo._2.substitute(a:= exists(y, forall(x, P(x) /\ Q(f(y)))), b := forall(y, exists(x, P(x) \/ R(y, x))), c:= forall(y, exists(x, Q(x) ==> R(x, y)) ))),
    ).flatten.zipWithIndex.map(f => (f._2, f._1, solve(() |- f._1)))
    println(s"First Order Easy Positive cases (${poseasy.size})")
    if poseasy.exists(f => !f._3) then 
        poseasy.foreach((i, f, b) => println(s"$i $b" + (if !b then s" $f" else "")))
    else println("All TRUE")
/*

    val negeasy = List(
        nega.map(fo => fo._2.substitute(a:= forall(x, P(x)), b := forall(x, Q(y)), c:= exists(x, R(x, x)) )),
        nega.map(fo => fo._2.substitute(a:= forall(x, P(x) /\ Q(f(x))), b := forall(x, P(g(x)) \/ R(y, x)), c:= exists(x, Q(x) ==> R(x, f(y))) )),
        nega.map(fo => fo._2.substitute(a:= exists(y, forall(x, P(x) /\ Q(f(y)))), b := forall(y, exists(x, P(g(x)) \/ R(y, x))), c:= forall(y, exists(x, Q(x) ==> R(x, f(y))) ))),
    ).flatten.zipWithIndex.map(f => (f._2, f._1, solve(() |- f._1)))
    println(s"First Order Easy Negative cases (${negeasy.size})")
    if negeasy.exists(f => f._3) then 
        negeasy.foreach((i, f, b) => println(s"$i $b" + (if b then s" $f" else "")))
    else println("All FALSE")
*/


    // First Order Hard, from https://isabelle.in.tum.de/library/FOL/FOL-ex/Quantifiers_Cla.html

    val poshard = List(
        forall(x, P(x) ==> Q(x)) ==> (forall(x, P(x)) ==> forall(x, Q(x))),
        forall(x, forall(y, R(x, y))) ==> forall(y, forall(x, R(x, y))),
        forall(x, forall(y, R(x, y))) ==> forall(y, forall(x, R(y, x))),
        exists(x, exists(y, R(x, y))) ==> exists(y, exists(x, R(x, y))),
        exists(x, exists(y, R(x, y))) ==> exists(y, exists(x, R(y, x))),
        (forall(x, P(x)) \/ forall(x, Q(x))) ==> forall(x, P(x) \/ Q(x)),
        forall(x, a ==> Q(x)) <=> (a ==> forall(x, Q(x))),
        forall(x, P(x) ==> a) <=> (exists(x, P(x)) ==> a),
        exists(x, P(x) \/ Q(x)) <=> (exists(x, P(x)) \/ exists(x, Q(x))),
        exists(x, P(x) /\ Q(x)) ==> (exists(x, P(x)) /\ exists(x, Q(x))),
        exists(y, forall(x, R(x, y))) ==> forall(x, exists(y, R(x, y))),
        forall(x, Q(x)) ==> exists(x, Q(x)),
        (forall(x, P(x) ==> Q(x)) /\ exists(x, P(x))) ==> exists(x, Q(x)),
        ((a ==> exists(x, Q(x))) /\ a) ==> exists(x, Q(x)),
        forall(x, P(x) ==> Q(f(x))) /\ forall(x, Q(x) ==> R(g(x), x)) ==> (P(y) ==> R(g(f(y)), f(y))),
        forall(x, forall(y, P(x) ==> Q(y))) ==> (exists(x, P(x)) ==> forall(y, Q(y))),
        (exists(x, P(x)) ==> forall(y, Q(y))) ==> forall(x, forall(y, P(x) ==> Q(y))),
        forall(x, forall(y, P(x) ==> Q(y))) <=> (exists(x, P(x)) ==> forall(y, Q(y))),
        exists(x, exists(y, P(x) /\ R(x, y))) ==> (exists(x, P(x) /\ exists(y, R(x, y)))),
        (exists(x, P(x) /\ exists(y, R(x, y)))) ==> exists(x, exists(y, P(x) /\ R(x, y))),
        exists(x, exists(y, P(x) /\ R(x, y))) <=> (exists(x, P(x) /\ exists(y, R(x, y)))),
        exists(y, forall(x, P(x) ==> R(x, y))) ==> (forall(x, P(x)) ==> exists(y, R(x, y))),
    ).zipWithIndex.map(f => (f._2, f._1, {solve(() |- f._1)}))
    println(s"First Order Hard Positive cases (${poshard.size})")
    if poshard.exists(f => !f._3) then 
        poshard.foreach((i, f, b) => println(s"$i $b" + (if !b then s" $f" else "")))
    else println("All TRUE")


/*

    val neghard = List(
        forall(x, exists(y, R(x, y))) ==> exists(y, forall(x, R(x, y))),
        exists(x, Q(x)) ==> forall(x, Q(x)),
        P(x) ==> forall(x, P(x)),
        (P(x) ==> forall(x, Q(x))) ==> forall(x, P(x) ==> Q(x)),
    ).zipWithIndex.map(f => (f._2, f._1, solve(() |- f._1)))
    println(s"First Order Hard Negative cases (${neghard.size})")
    if neghard.exists(f => f._3) then 
        neghard.foreach((i, f, b) => println(s"$i $b" + (if b then s" $f" else "")))
    else println("All FALSE")



*/


/*
    val form = exists(x, exists(y, P(x) /\ R(x, y))) <=> (exists(x, P(x) /\ exists(y, R(x, y))))

    doprint=true
    println("\nAnalysis\n")
    println(solve(() |- form))
*/

    //forall(x, P(x) ==> Q(x)) ==> (forall(x, P(x)) ==> forall(x, Q(x))),
}

