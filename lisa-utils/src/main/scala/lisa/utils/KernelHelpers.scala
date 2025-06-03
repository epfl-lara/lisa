package lisa.utils

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.kernel.proof.SCProofCheckerJudgement.SCInvalidProof
import lisa.kernel.proof.SCProofCheckerJudgement.SCValidProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.proof.*

import scala.annotation.targetName
import lisa.utils.unification.UnificationUtils.matchExpr
/**
 * A helper file that provides various syntactic sugars for LISA's FOL and proofs at the Kernel level.
 */
object KernelHelpers {

  def predicateType(arity: Int) = Range(0, arity).foldLeft(Prop: Sort)((acc, _) => Ind -> acc)
  def functionType(arity: Int) = Range(0, arity).foldLeft(Ind: Sort)((acc, _) => Ind -> acc)

  /////////////////
  // FOL helpers //
  /////////////////

  /* Prefix syntax */

  extension (s: Sort) {
    def >>:(t: Sort) : Sort = Arrow(s, t)
  }

  val Equality = equality
  val === = equality
  val ⊤ : Expression = top
  val ⊥ : Expression = bot
  val True: Expression = top
  val False: Expression = bot

  val ¬ = neg
  val ! = neg
  val /\ = and
  val \/ = or
  val ==> = implies
  val <=> = iff
  val ∀ = forall
  val ∃ = exists
  val ε = epsilon



  // UnapplyMethods

  object And :
    def unapply(e: Expression): Option[(Expression, Expression)] = e match 
      case Application(Application(`and`, l), r) => Some((l, r))
      case _ => None

  object Or :
    def unapply(e: Expression): Option[(Expression, Expression)] = e match
      case Application(Application(`or`, l), r) => Some((l, r))
      case _ => None

  object Neg :
    def unapply(e: Expression): Option[Expression] = e match
      case Application(`neg`, a) => Some(a)
      case _ => None
      
  object Implies :
    def unapply(e: Expression): Option[(Expression, Expression)] = e match
      case Application(Application(`implies`, l), r) => Some((l, r))
      case _ => None

  object Iff :
    def unapply(e: Expression): Option[(Expression, Expression)] = e match
      case Application(Application(`iff`, l), r) => Some((l, r))
      case _ => None

  object Forall :
    def unapply(e: Expression): Option[(Variable, Expression)] = e match
      case Application(`forall`, Lambda(x, inner)) => Some((x, inner))
      case _ => None

  object Exists :
    def unapply(e: Expression): Option[(Variable, Expression)] = e match
      case Application(`exists`, Lambda(x, inner)) => Some((x, inner))
      case _ => None

  object Epsilon :
    def unapply(e: Expression): Option[(Variable, Expression)] = e match
      case Application(`epsilon`, Lambda(x, inner)) => Some((x, inner))
      case _ => None

  object Multiand :
    def unapply(e: Expression): Option[Seq[Expression]] = e match
      case Application(Application(`and`, l), r) => Some(l +: unapply(r).getOrElse(Seq(r)))
      case _ => None
  
  object Multior :
    def unapply(e: Expression): Option[Seq[Expression]] = e match
      case Application(Application(`or`, l), r) => Some(l +: unapply(r).getOrElse(Seq(r)))
      case _ => None

  object Multiapp :
    def unapply(e: Expression): Option[(Expression, Seq[Expression])] = 
      def inner(e: Expression): Option[List[Expression]] = e match 
        case Application(f, arg) => inner(f) map (l => arg :: l)
        case _ => Some(List(e))
      val r = inner(e)
      r match
        case Some(l) if l.size > 1 => 
          val rev = l.reverse
          Some(rev.head, rev.tail)
        case _ => None




  def multiand(args: Seq[Expression]): Expression = args.reduceLeft(and(_)(_))
  def multior(args: Seq[Expression]): Expression = args.reduceLeft(or(_)(_))
  def multiapply(f: Expression)(args: Seq[Expression]): Expression = args.foldLeft(f)(_(_))

  /* Infix syntax */


  extension (e: exists.type) 
    @targetName("existsApply")
    def apply(v: Variable, inner: Expression): Expression = exists(lambda(v, inner))

  extension (e: forall.type)
    @targetName("forallApply")
    def apply(v: Variable, inner: Expression): Expression = forall(lambda(v, inner))
  
  extension (e: epsilon.type)
    @targetName("epsilonApply")
    def apply(v: Variable, inner: Expression): Expression = epsilon(lambda(v, inner))
  

  extension (f: Expression) {
    def apply(args: Expression*): Expression = multiapply(f)(args)
    def unary_! = neg(f)
    infix inline def ==>(g: Expression): Expression = implies(f)(g)
    infix inline def <=>(g: Expression): Expression = iff(f)(g)
    infix inline def /\(g: Expression): Expression = and(f)(g)
    infix inline def \/(g: Expression): Expression = or(f)(g)
    infix def ===(g: Expression): Expression = equality(f)(g)
    infix def ＝(g: Expression): Expression = equality(f)(g)

    def maxVarId(): Int = f match {
      case Variable(id, _) => id.no+1
      case Constant(_, _) => 0
      case Application(f, arg) => f.maxVarId() max arg.maxVarId()
      case Lambda(v, inner) => v.id.no max inner.maxVarId()
    }

    def leadingVars(): List[Variable] = 
      def recurse(e:Expression) : List[Variable] = e match {
        case Lambda(v, inner) => v :: recurse(inner)
        case _ => Nil
      }
      recurse(f).reverse

    def repr: String = f match
      case equality(a, b) => s"${a.repr} === ${b.repr}"
      case neg(a) => s"!${a.repr}"
      case and(a, b) => s"(${a.repr} /\\ ${b.repr})"
      case or(a, b) => s"(${a.repr} \\/ ${b.repr})"
      case implies(a, b) => s"(${a.repr} ==> ${b.repr})"
      case iff(a, b) => s"(${a.repr} <=> ${b.repr})"
      case forall(v, inner) => s"(forall(${v.repr}, ${inner.repr})"
      case exists(v, inner) => s"(exists(${v.repr}, ${inner.repr})"
      case epsilon(v, inner) => s"(epsilon(${v.repr}, ${inner.repr})"

      case Application(f, arg) => s"${f.repr}(${arg.repr})"
      case Constant(id, sort) => id.toString
      case Lambda(v, body) => s"lambda(${v.repr}, ${body.repr})"
      case Variable(id, sort) => id.toString

    def fullRepr: String = f match
      case Application(f, arg) => s"${f.fullRepr}(${arg.fullRepr})"
      case Constant(id, sort) => s"cst(${id},${sort})"
      case Lambda(v, body) => s"λ${v.fullRepr}.${body.fullRepr}"
      case Variable(id, sort) => s"v(${id},${sort})" 
  }

  extension (se: SimpleExpression) {
    def repr: String = se match
      case SimpleAnd(children, polarity) => 
        val pol = if polarity then "" else "!"
        s"${pol}and(${children.map(_.repr).mkString(", ")})"
      case SimpleForall(x, inner, polarity) => 
        val pol = if polarity then "" else "!"
        s"${pol}∀$x.${inner.repr}"
      case SimpleLiteral(polarity) => 
        val pol = if polarity then "" else "!"
        s"${pol}lit"
      case SimpleEquality(left, right, polarity) => 
        val pol = if polarity then "" else "!"
        s"${pol}(${left.repr} === ${right.repr})"
      case SimpleVariable(id, sort, polarity) => 
        val pol = if polarity then "" else "!"
        s"${pol}${id}"
      case SimpleBoundVariable(no, sort, polarity) => 
        val pol = if polarity then "" else "!"
        s"${pol}bv$no"
      case SimpleConstant(id, sort, polarity) => 
        val pol = if polarity then "" else "!"
        s"${pol}${id}"
      case SimpleApplication(arg1, arg2, polarity) => 
        val pol = if polarity then "" else "!"
        s"${pol}(${arg1.repr}(${arg2.repr}))"
      case SimpleLambda(x, inner) => 
        s"λ${x.repr}.${inner.repr}"


  }

  /* Conversions */

  /*
  given Conversion[(Boolean, List[Int], String), Option[(List[Int], String)]] = tr => if (tr._1) None else Some(tr._2, tr._3)
*/
  given Conversion[Expression, Sequent] = () |- _

  /* Sequents */

  val emptySeq: Sequent = Sequent(Set.empty, Set.empty)

  extension (s: Sequent) {
    // non OL-based / naive Sequent manipulation
    infix def +<<(f: Expression): Sequent = s.copy(left = s.left + f)
    infix def -<<(f: Expression): Sequent = s.copy(left = s.left - f)
    infix def +>>(f: Expression): Sequent = s.copy(right = s.right + f)
    infix def ->>(f: Expression): Sequent = s.copy(right = s.right - f)
    infix def ++<<(s1: Sequent): Sequent = s.copy(left = s.left ++ s1.left)
    infix def --<<(s1: Sequent): Sequent = s.copy(left = s.left -- s1.left)
    infix def ++>>(s1: Sequent): Sequent = s.copy(right = s.right ++ s1.right)
    infix def -->>(s1: Sequent): Sequent = s.copy(right = s.right -- s1.right)
    infix def ++(s1: Sequent): Sequent = s.copy(left = s.left ++ s1.left, right = s.right ++ s1.right)
    infix def --(s1: Sequent): Sequent = s.copy(left = s.left -- s1.left, right = s.right -- s1.right)

    // OL-based Sequent manipulation
    infix def removeLeft(f: Expression): Sequent = s.copy(left = s.left.filterNot(isSame(_, f)))
    infix def removeRight(f: Expression): Sequent = s.copy(right = s.right.filterNot(isSame(_, f)))
    infix def removeAllLeft(s1: Sequent): Sequent = s.copy(left = s.left.filterNot(e1 => s1.left.exists(e2 => isSame(e1, e2))))
    infix def removeAllLeft(s1: Set[Expression]): Sequent = s.copy(left = s.left.filterNot(e1 => s1.exists(e2 => isSame(e1, e2))))
    infix def removeAllRight(s1: Sequent): Sequent = s.copy(right = s.right.filterNot(e1 => s1.right.exists(e2 => isSame(e1, e2))))
    infix def removeAllRight(s1: Set[Expression]): Sequent = s.copy(right = s.right.filterNot(e1 => s1.exists(e2 => isSame(e1, e2))))
    infix def removeAll(s1: Sequent): Sequent = s.copy(left = s.left.filterNot(e1 => s1.left.exists(e2 => isSame(e1, e2))), right = s.right.filterNot(e1 => s1.right.exists(e2 => isSame(e1, e2))))

    infix def addLeftIfNotExists(f: Expression): Sequent = if (s.left.exists(isSame(_, f))) s else (s +<< f)
    infix def addRightIfNotExists(f: Expression): Sequent = if (s.right.exists(isSame(_, f))) s else (s +>> f)
    infix def addAllLeftIfNotExists(s1: Sequent): Sequent = s ++<< s1.copy(left = s1.left.filterNot(e1 => s.left.exists(isSame(_, e1))))
    infix def addAllRightIfNotExists(s1: Sequent): Sequent = s ++>> s1.copy(right = s1.right.filterNot(e1 => s.right.exists(isSame(_, e1))))
    infix def addAllIfNotExists(s1: Sequent): Sequent = s ++ s1.copy(left = s1.left.filterNot(e1 => s.left.exists(isSame(_, e1))), right = s1.right.filterNot(e1 => s.right.exists(isSame(_, e1))))

    // OL shorthands
    infix def +<?(f: Expression): Sequent = s addLeftIfNotExists f
    infix def -<?(f: Expression): Sequent = s removeLeft f
    infix def +>?(f: Expression): Sequent = s addRightIfNotExists f
    infix def ->?(f: Expression): Sequent = s removeRight f
    infix def ++<?(s1: Sequent): Sequent = s addAllLeftIfNotExists s1
    infix def --<?(s1: Sequent): Sequent = s removeAllLeft s1
    infix def ++>?(s1: Sequent): Sequent = s addAllRightIfNotExists s1
    infix def -->?(s1: Sequent): Sequent = s removeAllRight s1
    infix def --?(s1: Sequent): Sequent = s removeAll s1
    infix def ++?(s1: Sequent): Sequent = s addAllIfNotExists s1

    def repr: String = s"${s.left.map(_.repr).mkString(", ")} |- ${s.right.map(_.repr).mkString(", ")}"
    
    def fullRepr: String = s"${s.left.map(_.fullRepr).mkString(", ")} |- ${s.right.map(_.fullRepr).mkString(", ")}"
  }

  /**
   * Represents a converter of some object into a set.
   * @tparam S The type of elements in that set
   * @tparam T The type to convert from
   */
  protected trait FormulaSetConverter[T] {
    def apply(t: T): Set[Expression]
  }

  given FormulaSetConverter[Unit] with {
    override def apply(u: Unit): Set[Expression] = Set.empty
  }

  given FormulaSetConverter[EmptyTuple] with {
    override def apply(t: EmptyTuple): Set[Expression] = Set.empty
  }

  given [H <: Expression, T <: Tuple](using c: FormulaSetConverter[T]): FormulaSetConverter[H *: T] with {
    override def apply(t: H *: T): Set[Expression] = c.apply(t.tail) + t.head
  }

  given formula_to_set[T <: Expression]: FormulaSetConverter[T] with {
    override def apply(f: T): Set[Expression] = Set(f)
  }

  given [T <: Expression, I <: Iterable[T]]: FormulaSetConverter[I] with {
    override def apply(s: I): Set[Expression] = s.toSet
  }

  private def any2set[A, T <: A](any: T)(using c: FormulaSetConverter[T]): Set[Expression] = c.apply(any)

  extension [A, T1 <: A](left: T1)(using FormulaSetConverter[T1]) {
    infix def |-[B, T2 <: B](right: T2)(using FormulaSetConverter[T2]): Sequent = Sequent(any2set(left), any2set(right))
    infix def ⊢[B, T2 <: B](right: T2)(using FormulaSetConverter[T2]): Sequent = Sequent(any2set(left), any2set(right))
  }

  // Instatiation functions for formulas lifted to sequents.

  def substituteVariablesInSequent(s: Sequent, m: Map[Variable, Expression]): Sequent = {
    s.left.map(phi => substituteVariables(phi, m)) |- s.right.map(phi => substituteVariables(phi, m))
  }

  //////////////////////
  // SCProofs helpers //
  //////////////////////
  extension (sp: SCSubproof) {

    /**
     * Explore a proof with a specific path and returns the pointed proofstep.
     * @param path A path through subproofs of a proof.
     */
    def followPath(path: Seq[Int]): SCProofStep = path match {
      case Nil => sp
      case n :: Nil => sp.sp(n)
      case n :: ns =>
        assert(sp.sp.steps(n).isInstanceOf[SCSubproof], s"Got $path but next step is not a subproof: ${sp.sp.steps(n).getClass}")
        sp.sp.steps(n).asInstanceOf[SCSubproof].followPath(ns)
    }
  }

  extension (p: SCProof) {

    /**
     * Explore a proof with a specific path and returns the pointed proofstep.
     * @param path A path through subproofs of a proof.
     */
    def followPath(path: Seq[Int]): SCProofStep = SCSubproof(p, p.imports.indices).followPath(path)
  }

/*
  // Conversion from pairs (e.g. x -> f(x)) to lambdas
  given Conversion[Expression, LambdaTermTerm] = LambdaTermTerm(Seq(), _)
  given Conversion[VariableLabel, LambdaTermTerm] = a => LambdaTermTerm(Seq(), a: Expression)
  given Conversion[(VariableLabel, Expression), LambdaTermTerm] = a => LambdaTermTerm(Seq(a._1), a._2)
  given Conversion[(Seq[VariableLabel], Expression), LambdaTermTerm] = a => LambdaTermTerm(a._1, a._2)

  given Conversion[Expression, LambdaTermFormula] = LambdaTermFormula(Seq(), _)
  given Conversion[(VariableLabel, Expression), LambdaTermFormula] = a => LambdaTermFormula(Seq(a._1), a._2)
  given Conversion[(Seq[VariableLabel], Expression), LambdaTermFormula] = a => LambdaTermFormula(a._1, a._2)

  given Conversion[Expression, LambdaFormulaFormula] = LambdaFormulaFormula(Seq(), _)
  given Conversion[(VariableFormulaLabel, Expression), LambdaFormulaFormula] = a => LambdaFormulaFormula(Seq(a._1), a._2)
  given Conversion[(Seq[VariableFormulaLabel], Expression), LambdaFormulaFormula] = a => LambdaFormulaFormula(a._1, a._2)

  def 
  // Shortcut for LambdaTermTerm, LambdaTermFormula and LambdaFormulaFormula construction
  def lambda(x: VariableLabel, t: Expression): LambdaTermTerm = LambdaTermTerm(Seq(x), t)
  def lambda(xs: Seq[VariableLabel], t: Expression): LambdaTermTerm = LambdaTermTerm(xs, t)
  def lambda(x: VariableLabel, l: LambdaTermTerm): LambdaTermTerm = LambdaTermTerm(Seq(x) ++ l.vars, l.body)
  def lambda(xs: Seq[VariableLabel], l: LambdaTermTerm): LambdaTermTerm = LambdaTermTerm(xs ++ l.vars, l.body)

  def lambda(x: VariableLabel, phi: Expression): LambdaTermFormula = LambdaTermFormula(Seq(x), phi)
  def lambda(xs: Seq[VariableLabel], phi: Expression): LambdaTermFormula = LambdaTermFormula(xs, phi)
  def lambda(x: VariableLabel, l: LambdaTermFormula): LambdaTermFormula = LambdaTermFormula(Seq(x) ++ l.vars, l.body)
  def lambda(xs: Seq[VariableLabel], l: LambdaTermFormula): LambdaTermFormula = LambdaTermFormula(xs ++ l.vars, l.body)

  def lambda(X: VariableFormulaLabel, phi: Expression): LambdaFormulaFormula = LambdaFormulaFormula(Seq(X), phi)
  def lambda(Xs: Seq[VariableFormulaLabel], phi: Expression): LambdaFormulaFormula = LambdaFormulaFormula(Xs, phi)
  def lambda(X: VariableFormulaLabel, l: LambdaFormulaFormula): LambdaFormulaFormula = LambdaFormulaFormula(Seq(X) ++ l.vars, l.body)
  def lambda(Xs: Seq[VariableFormulaLabel], l: LambdaFormulaFormula): LambdaFormulaFormula = LambdaFormulaFormula(Xs ++ l.vars, l.body)
*/
  def lambda(x: Variable, t: Expression): Lambda = Lambda(x, t)
  def lambda(xs: Seq[Variable], t: Expression): Expression = xs.foldRight(t)((x, t) => Lambda(x, t))
  def reduceLambda(f: Lambda, t: Expression): Expression = substituteVariables(f.body, Map(f.v -> t))

  // declare symbols easily: "val x = variable;"
  def HOvariable(using name: sourcecode.Name)(sort: Sort): Variable = Variable(name.value, sort)
  def variable(using name: sourcecode.Name): Variable = Variable(name.value, Ind)
  def function(arity: Integer)(using name: sourcecode.Name): Variable = Variable(name.value, Range(0, arity).foldLeft(Ind: Sort)((acc, _)=> Ind -> acc))
  def formulaVariable(using name: sourcecode.Name): Variable = Variable(name.value, Prop)
  def predicate(arity: Integer)(using name: sourcecode.Name): Variable = Variable(name.value, Range(0, arity).foldLeft(Prop: Sort)((acc, _)=> Ind -> acc))
  def connector(arity: Integer)(using name: sourcecode.Name): Variable = Variable(name.value, Range(0, arity).foldLeft(Prop: Sort)((acc, _)=> Prop -> acc))
  def cst(using name: sourcecode.Name)(sort: Sort): Constant = Constant(name.value, sort)

  def HOvariable(sort: Sort)(id: Identifier): Variable = Variable(id, sort)
  def variable(id: Identifier): Variable = Variable(id, Ind)
  def function(arity: Integer)(id: Identifier): Variable = Variable(id, Range(0, arity).foldLeft(Ind: Sort)((acc, _)=> Ind -> acc))
  def formulaVariable(id: Identifier): Variable = Variable(id, Prop)
  def predicate(arity: Integer)(id: Identifier): Variable = Variable(id, Range(0, arity).foldLeft(Prop: Sort)((acc, _)=> Ind -> acc))
  def connector(arity: Integer)(id: Identifier): Variable = Variable(id, Range(0, arity).foldLeft(Prop: Sort)((acc, _)=> Prop -> acc))
  def cst(id: Identifier, sort:Sort): Constant = Constant(id, sort)

  // Conversions from String to Identifier
  class InvalidIdentifierException(identifier: String, errorMessage: String) extends LisaException(errorMessage) {
    def showError: String = errorMessage
  }

  given Conversion[String, Identifier] = str => {
    val pieces = str.split(Identifier.counterSeparator)
    if (pieces.length == 1) {
      val name = pieces.head
      if (!Identifier.isValidIdentifier(name)) {
        val no: String = Identifier.forbiddenChars.mkString("")
        throw new InvalidIdentifierException(str, s"Identifier must not contain whitespaces nor symbols among $no.")
      }
      Identifier(name)
    } else if (pieces.length == 2) {
      val name = pieces.head
      val no = pieces(1)
      if (!no.forall(_.isDigit) || no.isEmpty || (no.length > 1 && no.head == '0')) {
        throw new InvalidIdentifierException(str, s"The part of an identifier contained after ${Identifier.counterSeparator} must be a number without leading 0s.")
      }
      if (!Identifier.isValidIdentifier(name)) {
        val no: String = Identifier.forbiddenChars.mkString("")
        throw new InvalidIdentifierException(str, s"Identifier must not contain whitespaces nor symbols among $no.")
      }
      Identifier(name, no.toInt)
    } else { // if number of _ is greater than 1
      throw new InvalidIdentifierException("name", s"The identifier cannot contain more than one counter separator (${Identifier.counterSeparator}).")
    }
  }
  given Conversion[Identifier, String] = _.toString

  // Generates  new Identifier from an existing list
  def freshId(taken: Iterable[Identifier], base: Identifier): Identifier = {
    new Identifier(
      base.name,
      (taken.collect({ case Identifier(base.name, no) =>
        no
      }) ++ Iterable(base.no)).max + 1
    )
  }

  def nFreshId(taken: Iterable[Identifier], n: Int): IndexedSeq[Identifier] = {
    val max = if (taken.isEmpty) 0 else taken.map(c => c.no).max
    Range(0, n).map(i => Identifier("gen", max + i))
  }

  /////////////////////////////
  // RunningTheories Helpers //
  /////////////////////////////

  extension (theory: RunningTheory) {
    def makeAxiom(using name: sourcecode.Name)(formula: Expression): theory.Axiom = theory.addAxiom(name.value, formula) match {
      case Some(value) => value
      case None => throw new Exception("Axiom contains undefined symbols " + name.value + formula + theory)
    }

    /**
     * Add a theorem to the theory, but also asks explicitely for the desired conclusion
     * of the theorem to have more explicit writing and for sanity check.
     */
    def theorem(name: String, statement: Sequent, proof: SCProof, justifications: Seq[theory.Justification]): RunningTheoryJudgement[theory.Theorem] = {
      if (statement == proof.conclusion) theory.makeTheorem(name, statement, proof, justifications)
      else if (isSameSequent(statement, proof.conclusion)) theory.makeTheorem(name, statement, proof.appended(Restate(statement, proof.length - 1)), justifications)
      else InvalidJustification(s"The proof proves \n    ${proof.conclusion.repr}\ninstead of claimed \n    ${statement.repr}", None)
    }

    /**
     * Make a predicate definition in the theory, but only ask for the identifier of the new symbol; Arity is inferred
     * of the theorem to have more explicit writing and for sanity check. See also [[lisa.kernel.proof.RunningTheory.makePredicateDefinition]]
     */
    def definition(symbol: String, expression: Expression): RunningTheoryJudgement[theory.Definition] = {
      val label = Constant(symbol, expression.sort)
      val vars = expression.leadingVars()
      if (vars.length == expression.sort.depth) then
        theory.makeDefinition(label, expression, vars)
      else 
        var maxid = expression.maxVarId()-1
        val newvars = flatTypeParameters(expression.sort).drop(vars.length).map(t => {maxid+=1;Variable(Identifier("x", maxid), t)})
        theory.makeDefinition(label, expression, vars ++ newvars)
    }

    /**
     * Try to fetch, in this order, a justification that is an Axiom with the given name,
     * a Theorem with a given name or a Definition with a the given name as symbol
     */
    def getJustification(name: String): Option[theory.Justification] = theory.getAxiom(name).orElse(theory.getTheorem(name)).orElse(theory.getDefinition(name))

    /**
     * Verify if a given formula belongs to some language
     *
     * @param phi The formula to check
     * @return The List of undefined symols
     */
    def findUndefinedSymbols(phi: Expression): Set[Constant] = phi match {
      case Variable(id, sort) => Set.empty
      case cst: Constant => if (theory.isSymbol(cst)) Set.empty else Set(cst)
      case Lambda(v, inner) => findUndefinedSymbols(inner)
      case Application(f, arg) => findUndefinedSymbols(f) ++ findUndefinedSymbols(arg)
    }

    /**
     * Verify if a given sequent belongs to the language of the theory.
     *
     * @param s The sequent to check
     * @return The List of undefined symols
     */
    def findUndefinedSymbols(s: Sequent): Set[Constant] =
      s.left.flatMap(findUndefinedSymbols) ++ s.right.flatMap(findUndefinedSymbols)

  }

  extension (just: RunningTheory#Justification) {
    def repr: String = just match {
      case thm: RunningTheory#Theorem => s"  Theorem ${thm.name} := ${thm.proposition.repr}${if (thm.withSorry) " (!! Relies on Sorry)" else ""}\n"
      case axiom: RunningTheory#Axiom => s"  Axiom ${axiom.name} := ${axiom.ax.repr}\n"
      case d: RunningTheory#Definition =>
        s"  Definition of  symbol ${d.cst.id} : ${d.cst.sort} := ${d.expression}\n"

    }
  }

  extension [J <: RunningTheory#Justification](theoryJudgement: RunningTheoryJudgement[J]) {

    /**
     * If the Judgement is valid, show the inner justification and returns it.
     * Otherwise, om.output the error leading to the invalid justification and throw an error.
     */
    def repr: String = {
      theoryJudgement match {
        case RunningTheoryJudgement.ValidJustification(just) =>
          just.repr
        case InvalidJustification(message, error) =>
          s"$message\n${error match {
              case Some(judgement) => prettySCProof(judgement)
              case None => ""
            }}"
      }
    }
  }


  extension (judg: SCProofCheckerJudgement) {
    def repr: String = prettySCProof(judg)
  }


  /**
   * output a readable representation of a proof.
   */
  def checkProof(proof: SCProof, output: String => Unit = println): Unit = {
    val judgement = SCProofChecker.checkSCProof(proof)
    if judgement.isValid then
      output("Proof is valid")
    else
      output("Proof is invalid")
    val pl = proof.totalLength
    if pl > 100 then
      output("...")
      output(s"Proof is too long to be displayed [$pl steps]")
    else output(prettySCProof(judgement))
  }

  private def spaceSeparator(compact: Boolean): String = if (compact) "" else " "

  private def commaSeparator(compact: Boolean, symbol: String = ","): String = s"$symbol${spaceSeparator(compact)}"

  /**
   * Returns a string representation of this proof.
   *
   * @param proof     the proof
   * @param judgement optionally provide a proof checking judgement that will mark a particular step in the proof
   *                  (`->`) as an error. The proof is considered to be valid by default
   * @return a string where each indented line corresponds to a step in the proof
   */
  def prettySCProof(judgement: SCProofCheckerJudgement, forceDisplaySubproofs: Boolean = false): String = {
    val proof = judgement.proof
    def computeMaxNumberingLengths(proof: SCProof, level: Int, result: IndexedSeq[Int]): IndexedSeq[Int] = {
      val resultWithCurrent = result.updated(
        level,
        (Seq((proof.steps.size - 1).toString.length, result(level)) ++ (if (proof.imports.nonEmpty) Seq((-proof.imports.size).toString.length) else Seq.empty)).max
      )
      proof.steps.collect { case sp: SCSubproof => sp }.foldLeft(resultWithCurrent)((acc, sp) => computeMaxNumberingLengths(sp.sp, level + 1, if (acc.size <= level + 1) acc :+ 0 else acc))
    }

    val maxNumberingLengths = computeMaxNumberingLengths(proof, 0, IndexedSeq(0)) // The maximum value for each number column
    val maxLevel = maxNumberingLengths.size - 1

    def leftPadSpaces(v: Any, n: Int): String = {
      val s = String.valueOf(v)
      if (s.length < n) (" " * (n - s.length)) + s else s
    }

    def rightPadSpaces(v: Any, n: Int): String = {
      val s = String.valueOf(v)
      if (s.length < n) s + (" " * (n - s.length)) else s
    }

    def prettySCProofRecursive(proof: SCProof, level: Int, tree: IndexedSeq[Int], topMostIndices: IndexedSeq[Int]): Seq[(Boolean, String, String, String)] = {
      val printedImports = proof.imports.zipWithIndex.reverse.flatMap { case (imp, i) =>
        val currentTree = tree :+ (-i - 1)
        val showErrorForLine = judgement match {
          case SCValidProof(_, _) => false
          case SCInvalidProof(proof, position, _) => currentTree.startsWith(position) && currentTree.drop(position.size).forall(_ == 0)
        }
        val prefix = (Seq.fill(level - topMostIndices.size)(None) ++ Seq.fill(topMostIndices.size)(None) :+ Some(-i - 1)) ++ Seq.fill(maxLevel - level)(None)
        val prefixString = prefix.map(_.map(_.toString).getOrElse("")).zipWithIndex.map { case (v, i1) => leftPadSpaces(v, maxNumberingLengths(i1)) }.mkString(" ")

        def pretty(stepName: String, topSteps: Int*): (Boolean, String, String, String) =
          (
            showErrorForLine,
            prefixString,
            Seq(stepName, topSteps.mkString(commaSeparator(compact = false))).filter(_.nonEmpty).mkString(" "),
            imp.repr
          )

        Seq(pretty("Import", 0))
      }
      printedImports ++ proof.steps.zipWithIndex.flatMap { case (step, i) =>
        val currentTree = tree :+ i
        val showErrorForLine = judgement match {
          case SCValidProof(_, _) => false
          case SCInvalidProof(proof, position, _) => 
            currentTree.startsWith(position) && currentTree.drop(position.size).forall(_ == 0)
        }
        val prefix = (Seq.fill(level - topMostIndices.size)(None) ++ Seq.fill(topMostIndices.size)(None) :+ Some(i)) ++ Seq.fill(maxLevel - level)(None)
        val prefixString = prefix.map(_.map(_.toString).getOrElse("")).zipWithIndex.map { case (v, i1) => leftPadSpaces(v, maxNumberingLengths(i1)) }.mkString(" ")

        def pretty(stepName: String, topSteps: Int*): (Boolean, String, String, String) =
          (
            showErrorForLine,
            prefixString,
            Seq(stepName, topSteps.mkString(commaSeparator(compact = false))).filter(_.nonEmpty).mkString(" "),
            step.bot.repr
          )

        step match {
          case sp @ SCSubproof(_, _) =>
            pretty("Subproof", sp.premises*) +: prettySCProofRecursive(sp.sp, level + 1, currentTree, (if (i == 0) topMostIndices else IndexedSeq.empty) :+ i)
          case other =>
            val line = other match {
              case Restate(_, t1) => pretty("Rewrite", t1)
              case RestateTrue(_) => pretty("RewriteTrue")
              case Hypothesis(_, _) => pretty("Hypo.")
              case Cut(_, t1, t2, _) => pretty("Cut", t1, t2)
              case LeftAnd(_, t1, _, _) => pretty("Left ∧", t1)
              case LeftNot(_, t1, _) => pretty("Left ¬", t1)
              case RightOr(_, t1, _, _) => pretty("Right ∨", t1)
              case RightNot(_, t1, _) => pretty("Right ¬", t1)
              case LeftExists(_, t1, _, _) => pretty("Left ∃", t1)
              case LeftForall(_, t1, _, _, _) => pretty("Left ∀", t1)
              case LeftOr(_, l, _) => pretty("Left ∨", l*)
              case RightExists(_, t1, _, _, _) => pretty("Right ∃", t1)
              case RightForall(_, t1, _, _) => pretty("Right ∀", t1)
              case RightEpsilon(_, t1, _, _, _) => pretty("Right ε", t1)
              case RightAnd(_, l, _) => pretty("Right ∧", l*)
              case RightIff(_, t1, t2, _, _) => pretty("Right ⇔", t1, t2)
              case RightImplies(_, t1, _, _) => pretty("Right ⇒", t1)
              case LeftImplies(_, t1, t2, _, _) => pretty("Left ⇒", t1, t2)
              case LeftIff(_, t1, _, _) => pretty("Left ⇔", t1)
              case Weakening(_, t1) => pretty("Weakening", t1)
              case Beta(_, t1) => pretty("Beta", t1)
              case LeftRefl(_, t1, _) => pretty("L. Refl", t1)
              case RightRefl(_, _) => pretty("R. Refl")
              case LeftSubstEq(_, t1, _, _) => pretty("L. SubstEq", t1)
              case RightSubstEq(_, t1, _, _) => pretty("R. SubstEq", t1)
              case InstSchema(_, t1, _) => pretty("Schema Instantiation", t1)
              case Sorry(_) => pretty("Sorry")
              case SCSubproof(_, _) => throw new Exception("Should not happen")
            }
            Seq(line)
        }
      }
    }

    val marker = "->"

    val lines = prettySCProofRecursive(proof, 0, IndexedSeq.empty, IndexedSeq.empty)
    val maxStepNameLength = lines.map { case (_, _, stepName, _) => stepName.length }.maxOption.getOrElse(0)
    lines
      .map { case (isMarked, indices, stepName, sequent) =>
        val suffix = Seq(indices, rightPadSpaces(stepName, maxStepNameLength), sequent)
        val full = if (!judgement.isValid) (if (isMarked) marker else leftPadSpaces("", marker.length)) +: suffix else suffix
        full.mkString(" ")
      }
      .mkString("\n") + (judgement match {
      case SCValidProof(_, _) => ""
      case SCInvalidProof(proof, path, message) => s"\nProof checker has reported an error at line ${path.mkString(".")}: $message"
    })
  }

  def prettySCProof(proof: SCProof): String = prettySCProof(SCValidProof(proof), false)


}
