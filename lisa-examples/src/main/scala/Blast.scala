
import lisa.utils.K.{_, given}
import lisa.utils.K
import scala.collection.immutable.HashSet

object Blast extends lisa.Main{
/*
    case class Branch(
        beta: List[NormalAnd],  //polarity = false
        delta: List[NormalForall],  //polarity = false
        gamma: List[NormalForall],  //polarity = true
        atoms: (List[NormalPredicate|NormalLiteral], List[NormalPredicate|NormalLiteral]),    // split into positive and negatives!
        knownSubst: Substitution,
        unifiable: List[Identifier]
        //active: List[NormalFormula], used: HashSet[Int], unifiable: HashSet[Identifier]
    ){
        def pop(f : NormalFormula) : Branch = f match
            case f @ NormalAnd(args, false) => if (beta.nonEmpty && beta.head.uniqueKey == f.uniqueKey) copy(beta=beta.tail) else throw Exception("First formula of beta is not f")
            case f @ NormalForall(x, inner, false) => if (delta.nonEmpty && delta.head.uniqueKey == f.uniqueKey) copy(delta=delta.tail) else throw Exception("First formula of delta is not f")
            case f @ NormalForall(x, inner, true) => if (gamma.nonEmpty && gamma.head.uniqueKey == f.uniqueKey) copy(gamma=gamma.tail) else throw Exception("First formula of gamma is not f")
            case NormalAnd(args, true) => throw Exception("Branches never contain alpha formulas")
            case f @ NormalLiteral(polarity) => throw Exception("Should not pop Literals")
            case f @ NormalPredicate(id, args, polarity) => throw Exception("Should not pop Atoms")
            case f @ NormalSchemConnector(id, args, polarity) => ???

        def prepended(f:NormalFormula) : Branch = f match
            case NormalAnd(args, true) => this.prependedAll(args)
            case f @ NormalAnd(args, false) => this.copy(beta = f :: beta)
            case f @ NormalLiteral(polarity) => if (polarity) this.copy(atoms = (f :: atoms._1, atoms._2)) else this.copy(atoms = (atoms._1, f :: atoms._2))
            case f @ NormalForall(x, inner, false) => this.copy(delta = f :: delta)
            case f @ NormalForall(x, inner, true) => this.copy(gamma = f :: gamma)
            case f @ NormalPredicate(id, args, polarity) => if (polarity) this.copy(atoms = (f :: atoms._1, atoms._2)) else this.copy(atoms = (atoms._1, f :: atoms._2))
            case f @ NormalSchemConnector(id, args, polarity) => ???

        def prependedAll(l: Seq[NormalFormula]) : Branch = l.foldLeft(this)((a, b) => a.prepended(b))
        
    }
    object Branch{
        def empty = Branch(Nil, Nil, Nil, (Nil, Nil), Substitution.empty, Nil)
    }
    
    def solve(S:Sequent):Boolean = {
        val ks = S.underlying
        val f = K.ConnectorFormula(K.And, (ks.left.toSeq ++ ks.right.map(f => K.ConnectorFormula(K.Neg, List(f)))))
        val nf = computeNormalForm(simplify(f))

        nf match
            case NormalAnd(args, true) => decide(Branch.empty.prependedAll(args))
            case _ => decide(Branch.empty.prepended(nf))
        
    }
    trait Substitution
    object Substitution{
        object empty extends Substitution
    }

    def unify(pos: NormalPredicate, neg: NormalPredicate, current: Substitution, unifiable: List[Identifier]): Option[Substitution] = {
        ???
    }

    //Find if a branch can be closed
    def close(branch: Branch) : List[Substitution] = {
        val pos = branch.atoms._1
        val neg = branch.atoms._2
        var substitutions: List[Substitution] = Nil
        if (neg.contains(NormalLiteral(false))) List(Substitution.empty)
        pos.foreach( p => p match
            case p : NormalPredicate => neg.foreach(n => n match 
                case n: NormalPredicate => 
                    unify(p, n, branch.knownSubst, branch.unifiable) match
                        case None => ()
                        case Some(unif) => substitutions = unif :: substitutions
                    
                case n: NormalLiteral => return List(Substitution.empty)
            )
            case p : NormalLiteral => ()
        )
        substitutions
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
                    getInverse(disjunct) match {
                        case NormalAnd(args, true) => b1.prependedAll(args)
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
            (b1.prepended(getInverse(f.inner)), true)
    }

    //Find a universally quantified variable
    //Add the unquantified formula to the branch and mark the bound variable as suitable for unification
    def gamma(branch: Branch):(Branch, Boolean) = {
        if (branch.gamma.isEmpty) (branch, false)
        else
            val f = branch.gamma.head
            val b1 = branch.copy(gamma = branch.gamma.tail, unifiable = f.x :: branch.unifiable)
            (b1.prepended(f.inner), true)
    }

    def decide(branch: Branch, remainingBranches: List[Branch], subst: Substitution): Iterator[Substitution] = {
        val it = close(branch).toIterator
        var res: Iterator[Substitution] = Iterator.empty
        while (it.hasNext && res.isEmpty) 
            res = decide(remainingBranches.head, remainingBranches.tail, it.next())
        if (res.nonEmpty) res 
        else if (branch.delta.nonEmpty) decide(delta(branch)._1, remainingBranches, subst)
        else if (branch.beta.nonEmpty)
            val list = beta(branch)
            decide(list.head, remainingBranches.prependedAll(list.tail), subst)
        else if (branch.gamma.nonEmpty) decide(gamma(branch)._1, remainingBranches, subst)
        else Iterator.empty
    }












    
    val a = formulaVariable
    val b = formulaVariable
    val c = formulaVariable
    val d = formulaVariable
    val e = formulaVariable
    val f = formulaVariable
    val g = formulaVariable
    val h = formulaVariable
    println("Positive cases")
    val posi = List(
        a <=> a,
        a \/ !a,
        ((a ==> b) /\ (b ==> c)) ==> (a ==> c),
        (a <=> b) <=> ((a/\b) \/ (!a /\ !b)),
        ((a ==> c) /\ (b ==> c)) <=> ((a \/ b) ==> c),
        ((a ==> b) /\ (c ==> d)) ==> ((a \/ c) ==> (b \/ d))
    )
    posi.foreach(f => println(solve(() |- f)))


    println("Negative cases")
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
    )
    nega.foreach(f => println(solve(() |- f)))
    




    /*
    def solve(f:Formula):Boolean = {
        computeNormalForm(simplify(f)) match
            case NormalAnd(args, true) => refute(args.toList)
            case nf => refute(List(nf))
    }

    def refute(branch:List[NormalFormula]): Boolean = {
        val betaCandidates = branch.collectFirst {case f @ NormalAnd(args, false) => f}
        checkForContradiction(NormalAnd(branch, true)) || (betaCandidates match
            case None => false
            case Some(value) => value.args.forall(disjunct => {
                val b = branch.filterNot(_ == value)
                refute(getInverse(disjunct) match {case NormalAnd(args, true) => b.prependedAll(args); case d => d :: b})
            }))
    }
    */

*/

}