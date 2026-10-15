package lisa.kernel.fol

import lisa.kernel.fol.Syntax

private[fol] trait OLEquivalenceChecker extends Syntax {

  /**
   * Returns the internal αβ-normal form of the given expression.
   */
  private[kernel] def simpleReducedForm(expr: Expression): SimpleExpression = {
    simplify(expr.betaNormalForm)
  }

  /**
   * Returns the reduced form of the given expression in AIG representation.
   *
   * Computes the internal normal form, then converts it back to an
   * [[Expression]] in AIG representation.
   */
  def reducedForm(expr: Expression): Expression = {
    val bnf = expr.betaNormalForm
    val p = simplify(bnf)
    val nf = computeNormalForm(p)
    val fln = fromLocallyNameless(nf, Map.empty, 0)
    val res = toExpressionAIG(fln)
    res
  }

  /**
   * Returns the reduced form of the given expression in NNF representation.
   *
   * Computes the internal normal form, then converts it back to an
   * [[Expression]] in NNF representation.
   */
  def reducedNNFForm(expr: Expression): Expression = {
    val bnf = expr.betaNormalForm
    val p = simplify(expr)
    val nf = computeNormalForm(p)
    val fln = fromLocallyNameless(nf, Map.empty, 0)
    val res = toExpressionNNF(fln, true)
    res
  }

  /**
   * Returns true if the two expressions are equivalent by the rules of the OL equivalence checker.
   *
   * The expressions are simplified and reduced to their orthologic normal form, and then compared.
   * This takes into account all the laws of ortholattices, symmetry and reflexivity of equality, alpha-beta-eta-equivalence, and unfolds ⇒, ⇔, ∃ using other connectives.
   */
  def isSame(e1: Expression, e2: Expression): Boolean = {
    if (e1.uniqueNumber == e2.uniqueNumber) true
    else {
      val nf1 = computeNormalForm(simplify(e1.betaNormalForm))
      val nf2 = computeNormalForm(simplify(e2.betaNormalForm))
      latticesEQ(nf1, nf2)
    }

  }

  /**
   * Returns true if the first expression implies the second by the rules of the OL equivalence checker.
   *
   * The two arguments must be expressions of type [[Prop]].
   *
   * @see [[isSame]]
   * @see [[isSubset]]
   * @see [[contains]]
   */
  def isImplying(e1: Expression, e2: Expression): Boolean = {
    require(e1.sort == Prop && e2.sort == Prop)
    if (e1.uniqueNumber == e2.uniqueNumber) true
    else {
      val nf1 = computeNormalForm(simplify(e1.betaNormalForm))
      val nf2 = computeNormalForm(simplify(e2.betaNormalForm))
      latticesLEQUnchecked(nf1, nf2)
    }
  }

  /**
   * Returns true if all the expressions in `s1` are equivalent to some expression in `s2`.
   *
   * @see [[isSame]]
   * @see [[isSubset]]
   * @see [[contains]]
   */
  def isSubset(s1: Set[Expression], s2: Set[Expression]): Boolean = {
    s1.forall(e1 => s2.exists(e2 => isSame(e1, e2)))
  }

  /**
   * Returns true if all the expressions in `s1` are equivalent to some expression in `s2` and vice versa.
   *
   * @see [[isSame]]
   * @see [[isSubset]]
   * @see [[contains]]
   */
  def isSameSet(s1: Set[Expression], s2: Set[Expression]): Boolean =
    isSubset(s1, s2) && isSubset(s2, s1)

  /**
   * Returns true if the set `s` contains an expression equivalent to `f`.
   *
   * @see [[isSame]]
   * @see [[isSubset]]
   * @see [[isSameSet]]
   */
  def contains(s: Set[Expression], f: Expression): Boolean = {
    s.exists(g => isSame(f, g))
  }

  /**
   * A counter for [[SimpleExpression]] instances. Used for efficient reference equality.
   */
  private var totSimpleExpr = 0

  /**
   * Represents [[Expression]]s in a polar normalized form where
   * - ⇒, ⇔, ∃, ∨ are unfolded using other connectives: ¬, ∧, ∀
   * - consecutive conjunctions are flattened
   * - double negations are eliminated
   */
  private[kernel] sealed abstract class SimpleExpression extends Product {

    // Equal trees can have different unique keys. Cache their structural hash instead.
    private lazy val cachedHashCode: Int = scala.util.hashing.MurmurHash3.productHash(this)

    final override def hashCode(): Int = cachedHashCode

    /**
     * The sort of the expression.
     */
    val sort: Sort

    /**
     * True if the expression contains formulas.
     */
    val containsFormulas: Boolean

    /**
     * A unique key for the expression, used for efficient reference equality checking.
     */
    val uniqueKey = totSimpleExpr
    totSimpleExpr += 1

    /**
     * The number of subterms which are actual concrete formulas.
     */
    // val size : Int
    private[OLEquivalenceChecker] var inverse: Option[SimpleExpression] = None
    private[OLEquivalenceChecker] var NNF_pos: Option[Expression] = None
    private[OLEquivalenceChecker] var NNF_neg: Option[Expression] = None
    private[OLEquivalenceChecker] var formulaAIG: Option[Expression] = None
    private[OLEquivalenceChecker] var normalForm: Option[SimpleExpression] = None
    private[OLEquivalenceChecker] var namelessForm: Option[SimpleExpression] = None
  }

  /**
   * Polar version of [[variable]] variable.
   */
  private[kernel] case class SimpleVariable(id: Identifier, sort: Sort, polarity: Boolean) extends SimpleExpression {
    val containsFormulas: Boolean = sort == Prop
  }

  /**
   * Polar version of [[Variable]] for a bound variable in locally nameless representation.
   */
  private[kernel] case class SimpleBoundVariable(no: Int, sort: Sort, polarity: Boolean) extends SimpleExpression {
    val containsFormulas: Boolean = sort == Prop
  }

  /**
   * Polar version of [[Constant]] for a constant.
   */
  private[kernel] case class SimpleConstant(id: Identifier, sort: Sort, polarity: Boolean) extends SimpleExpression {
    val containsFormulas: Boolean = sort == Prop
  }

  /**
   * Polar version of [[Application]] for an application of a function to an argument.
   */
  private[kernel] case class SimpleApplication(f: SimpleExpression, arg: SimpleExpression, polarity: Boolean) extends SimpleExpression {
    val sort = f.sort match
      case Arrow(from, to) if from == arg.sort => to
      case _ => throw new IllegalArgumentException(s"Application of $f to $arg is not legal")
    val containsFormulas: Boolean = sort == Prop || f.containsFormulas || arg.containsFormulas
  }

  /**
   * Polar version of [[Lambda]] for a lambda abstraction.
   */
  private[kernel] case class SimpleLambda(v: Variable, body: SimpleExpression) extends SimpleExpression {
    val containsFormulas: Boolean = body.containsFormulas
    val sort = (v.sort -> body.sort)
  }

  /**
   * Polar version of [[And]]```(_)(_)...```.
   */
  private[kernel] case class SimpleAnd(children: Seq[SimpleExpression], polarity: Boolean) extends SimpleExpression {
    val containsFormulas: Boolean = true
    val sort = Prop
  }

  /**
   * Polar version of [[Forall]]```Lambda(_, _)``` for a universal quantification.
   */
  private[kernel] case class SimpleForall(id: Identifier, body: SimpleExpression, polarity: Boolean) extends SimpleExpression {
    val containsFormulas: Boolean = true
    val sort = Prop
  }

  /**
   * Polar version of [[top]] and [[bot]].
   */
  private[kernel] case class SimpleLiteral(polarity: Boolean) extends SimpleExpression {
    val containsFormulas: Boolean = true
    val sort = Prop
  }

  /**
   * Polar version of [[Equality]]```(_)(_)``` for an equality.
   */
  private[kernel] case class SimpleEquality(left: SimpleExpression, right: SimpleExpression, polarity: Boolean) extends SimpleExpression {
    val containsFormulas: Boolean = true
    val sort = Prop
  }

  /**
   * Returns the negation of `e` in polar form. Use caching.
   */
  private[kernel] def getInversePolar(e: SimpleExpression): SimpleExpression = e.inverse match
    case Some(inverse) => inverse
    case None =>
      val inverse = e match {
        case e: SimpleAnd => e.copy(polarity = !e.polarity)
        case e: SimpleForall => e.copy(polarity = !e.polarity)
        case e: SimpleLiteral => e.copy(polarity = !e.polarity)
        case e: SimpleEquality => e.copy(polarity = !e.polarity)
        case e: SimpleVariable if e.sort == Prop => e.copy(polarity = !e.polarity)
        case e: SimpleBoundVariable if e.sort == Prop => e.copy(polarity = !e.polarity)
        case e: SimpleConstant if e.sort == Prop => e.copy(polarity = !e.polarity)
        case e: SimpleApplication if e.sort == Prop => e.copy(polarity = !e.polarity)
        case _ => throw new Exception("Cannot invert expression that is not a formula")
      }
      e.inverse = Some(inverse)
      inverse

  /**
   * Converts back a [[SimpleExpression]] to an [[Expression]] in AIG representation.
   */
  private[kernel] def toExpressionAIG(e: SimpleExpression): Expression =
    if e.formulaAIG.isDefined then e.formulaAIG.get
    else {
      val r: Expression = e match {
        case SimpleAnd(children, polarity) =>
          val f = children.map(toExpressionAIG).reduceLeft(and(_)(_))
          if (polarity) f else neg(f)
        case SimpleForall(x, body, polarity) =>
          val f = forall(Lambda(Variable(x, Ind), toExpressionAIG(body)))
          if (polarity) f else neg(f)
        case SimpleEquality(left, right, polarity) =>
          val f = equality(toExpressionAIG(left))(toExpressionAIG(right))
          if (polarity) f else neg(f)
        case SimpleLiteral(polarity) => if (polarity) top else bot
        case SimpleVariable(id, sort, polarity) => if (polarity) Variable(id, sort) else neg(Variable(id, sort))
        case SimpleBoundVariable(no, sort, polarity) => throw new Exception("This case should be unreachable. Can't call toFormulaAIG on a bound variable")
        case SimpleConstant(id, sort, polarity) => if (polarity) Constant(id, sort) else neg(Constant(id, sort))
        case SimpleApplication(f, arg, polarity) =>
          val g = Application(toExpressionAIG(f), toExpressionAIG(arg))
          if (polarity)
            g
          else
            neg(g)
        case SimpleLambda(v, body) => Lambda(v, toExpressionAIG(body))
      }
      e.formulaAIG = Some(r)
      r
    }

  /**
   * Converts a [[SimpleExpression]] to an [[Expression]] in NNF representation.
   */
  private[kernel] def toExpressionNNF(e: SimpleExpression, positive: Boolean): Expression = {
    if (positive) {
      if e.NNF_pos.isDefined then return e.NNF_pos.get
      if e.inverse.isDefined && e.inverse.get.NNF_neg.isDefined then return e.inverse.get.NNF_neg.get
    } else if (!positive) {
      if e.NNF_neg.isDefined then return e.NNF_neg.get
      if e.inverse.isDefined && e.inverse.get.NNF_pos.isDefined then return e.inverse.get.NNF_pos.get
    }
    val r = e match {
      case SimpleAnd(children, polarity) =>
        if (positive == polarity)
          children.map(toExpressionNNF(_, true)).reduceLeft(and(_)(_))
        else
          children.map(toExpressionNNF(_, false)).reduceLeft(or(_)(_))
      case SimpleForall(x, body, polarity) =>
        if (positive == polarity)
          forall(Lambda(Variable(x, Ind), toExpressionNNF(body, true))) // rebuilding variable not ideal
        else
          exists(Lambda(Variable(x, Ind), toExpressionNNF(body, false)))
      case SimpleEquality(left, right, polarity) =>
        if (positive == polarity)
          equality(toExpressionNNF(left, true))(toExpressionNNF(right, true))
        else
          neg(equality(toExpressionNNF(left, true))(toExpressionNNF(right, true)))
      case SimpleLiteral(polarity) =>
        if (positive == polarity) top
        else bot
      case SimpleVariable(id, sort, polarity) =>
        if (polarity == positive) Variable(id, sort)
        else neg(Variable(id, sort))
      case SimpleBoundVariable(no, sort, polarity) => throw new Exception("This case should be unreachable. Can't call toExpressionNNF on a bound variable")
      case SimpleConstant(id, sort, polarity) =>
        if (polarity == positive) Constant(id, sort)
        else neg(Constant(id, sort))
      case SimpleApplication(f, arg, polarity) =>
        if (polarity == positive)
          Application(toExpressionNNF(f, true), toExpressionNNF(arg, true))
        else
          neg(Application(toExpressionNNF(f, true), toExpressionNNF(arg, true)))
      case SimpleLambda(v, body) => Lambda(v, toExpressionNNF(body, true))
    }
    if (positive) e.NNF_pos = Some(r)
    else e.NNF_neg = Some(r)
    r
  }

  /**
   * Converts an [[Expression]] to a [[SimpleExpression]], where
   * - ⇒, ⇔, ∃, ∨ are unfolded using other connectives: ¬, ∧, ∀
   * - consecutive conjunctions are flattened
   * - double negations are eliminated
   */
  private[kernel] def polarize(e: Expression, polarity: Boolean): SimpleExpression = {
    if (polarity & e.polarExpr.isDefined) {
      e.polarExpr.get
    } else if (!polarity & e.polarExpr.isDefined) {
      getInversePolar(e.polarExpr.get)
    } else {
      val r = e match {
        case neg(arg) =>
          polarize(arg, !polarity)
        case implies(arg1, arg2) =>
          SimpleAnd(Seq(polarize(arg1, true), polarize(arg2, false)), !polarity)
        case iff(arg1, arg2) =>
          val l1 = polarize(arg1, true)
          val r1 = polarize(arg2, true)
          SimpleAnd(
            Seq(
              SimpleAnd(Seq(l1, getInversePolar(r1)), false),
              SimpleAnd(Seq(getInversePolar(l1), r1), false)
            ),
            polarity
          )
        case and(arg1, arg2) =>
          SimpleAnd(Seq(polarize(arg1, true), polarize(arg2, true)), polarity)
        case or(arg1, arg2) =>
          SimpleAnd(Seq(polarize(arg1, false), polarize(arg2, false)), !polarity)
        case forall(Lambda(v, body)) =>
          SimpleForall(v.id, polarize(body, true), polarity)
        case forall(p) =>
          val fresh = freshId(p.freeVariables.map(_.id), Identifier("x", 0))
          val newInner = polarize(Application(p, Variable(fresh, Ind)), true)
          SimpleForall(fresh, newInner, polarity)
        case exists(Lambda(v, body)) =>
          SimpleForall(v.id, polarize(body, false), !polarity)
        case exists(p) =>
          val fresh = freshId(p.freeVariables.map(_.id), Identifier("x", 0))
          val newInner = polarize(Application(p, Variable(fresh, Ind)), false)
          SimpleForall(fresh, newInner, !polarity)
        case equality(arg1, arg2) =>
          SimpleEquality(polarize(arg1, true), polarize(arg2, true), polarity)
        case Application(f, arg) =>
          SimpleApplication(polarize(f, true), polarize(arg, true), polarity)
        case Lambda(v, body) => SimpleLambda(v, polarize(body, true))
        case `top` => SimpleLiteral(polarity)
        case `bot` => SimpleLiteral(!polarity)
        case Constant(id, sort) => SimpleConstant(id, sort, polarity)
        case Variable(id, sort) => SimpleVariable(id, sort, polarity)
      }
      if (polarity) e.polarExpr = Some(r)
      else e.polarExpr = Some(getInversePolar(r))
      r
    }
  }

  /** Retain an application when both transformed children are unchanged. */
  private def reuseApplication(e: SimpleApplication, f: SimpleExpression, arg: SimpleExpression): SimpleExpression =
    if (e.f eq f) && (e.arg eq arg) then e else SimpleApplication(f, arg, e.polarity)

  /** Retain an abstraction when its transformed body is unchanged. */
  private def reuseLambda(e: SimpleLambda, body: SimpleExpression): SimpleExpression =
    if e.body eq body then e else SimpleLambda(e.v, body)

  /**
   * Replaces all [[SimpleVariable]]s with [[SimpleBoundVariable]]s in `e` using localy nameless (de Bruijn) representation.
   * @see [[fromLocallyNameless]]
   */
  private[kernel] def toLocallyNameless(e: SimpleExpression): SimpleExpression =
    e.namelessForm match
      case Some(value) => value
      case None =>
        val r = e match {
          case SimpleAnd(children, polarity) => SimpleAnd(children.map(toLocallyNameless), polarity)
          case SimpleForall(x, inner, polarity) => SimpleForall(x, toLocallyNameless2(inner, Map((x, Ind) -> 0), 1), polarity)
          case e: SimpleLiteral => e
          case SimpleEquality(left, right, polarity) => SimpleEquality(toLocallyNameless(left), toLocallyNameless(right), polarity)
          case v: SimpleVariable => v
          case s: SimpleBoundVariable => throw new Exception("This case should be unreachable. Can't call toLocallyNameless on a bound variable")
          case e: SimpleConstant => e
          case e: SimpleApplication => reuseApplication(e, toLocallyNameless(e.f), toLocallyNameless(e.arg))
          case e: SimpleLambda => reuseLambda(e, toLocallyNameless2(e.body, Map((e.v.id, e.v.sort) -> 0), 1))
        }
        e.namelessForm = Some(r)
        r

  /**
   * Replaces all [[SimpleVariable]]s with [[SimpleBoundVariable]]s in `e` using localy nameless (de Bruijn) representation.
   */
  private[kernel] def toLocallyNameless2(e: SimpleExpression, subst: Map[(Identifier, Sort), Int], i: Int): SimpleExpression = e match {
    case SimpleAnd(children, polarity) => SimpleAnd(children.map(toLocallyNameless2(_, subst, i)), polarity)
    case SimpleForall(x, inner, polarity) => SimpleForall(x, toLocallyNameless2(inner, subst + ((x, Ind) -> i), i + 1), polarity)
    case e: SimpleLiteral => e
    case SimpleEquality(left, right, polarity) => SimpleEquality(toLocallyNameless2(left, subst, i), toLocallyNameless2(right, subst, i), polarity)
    case v: SimpleVariable =>
      if (subst.contains((v.id, v.sort))) SimpleBoundVariable(i - subst((v.id, v.sort)), v.sort, v.polarity)
      else v
    case s: SimpleBoundVariable => throw new Exception("This case should be unreachable. Can't call toLocallyNameless on a bound variable")
    case e: SimpleConstant => e
    case e: SimpleApplication => reuseApplication(e, toLocallyNameless2(e.f, subst, i), toLocallyNameless2(e.arg, subst, i))
    case e: SimpleLambda => reuseLambda(e, toLocallyNameless2(e.body, subst + ((e.v.id, e.v.sort) -> i), i + 1))
  }

  /**
   * Replaces all [[SimpleBoundVariable]]s with [[SimpleVariable]]s in `e`, reverting localy nameless representation.
   * @see [[toLocallyNameless]]
   */
  private[kernel] def fromLocallyNameless(e: SimpleExpression, subst: Map[Int, (Identifier, Sort)], i: Int): SimpleExpression = e match {
    case SimpleAnd(children, polarity) => SimpleAnd(children.map(fromLocallyNameless(_, subst, i)), polarity)
    case SimpleForall(x, inner, polarity) => SimpleForall(x, fromLocallyNameless(inner, subst + (i -> (x, Ind)), i + 1), polarity)
    case e: SimpleLiteral => e
    case SimpleEquality(left, right, polarity) => SimpleEquality(fromLocallyNameless(left, subst, i), fromLocallyNameless(right, subst, i), polarity)
    case SimpleBoundVariable(no, sort, polarity) =>
      val dist = i - no
      if (subst.contains(dist)) { val (id, sort) = subst(dist); SimpleVariable(id, sort, polarity) }
      else throw new Exception("This case should be unreachable, error")
    case v: SimpleVariable => v
    case e: SimpleConstant => e
    case e: SimpleApplication => reuseApplication(e, fromLocallyNameless(e.f, subst, i), fromLocallyNameless(e.arg, subst, i))
    case e: SimpleLambda => reuseLambda(e, fromLocallyNameless(e.body, subst + (i -> (e.v.id, e.v.sort)), i + 1))
  }

  /**
   * Simplifies an [[Expression]] to a [[SimpleExpression]] using [[polarize]] and [[toLocallyNameless]].
   */
  private[kernel] def simplify(e: Expression): SimpleExpression = toLocallyNameless(polarize(e, true))

  //////////////////////
  //// OL Algorithm ////
  //////////////////////

  /**
   * Computes the OL normal form of `e` modulo Orthologic. Uses caching.
   */
  private[kernel] def computeNormalForm(e: SimpleExpression): SimpleExpression = {
    e.normalForm match
      case Some(value) => value
      case None =>
        val r: SimpleExpression = e match {
        case SimpleAnd(children, polarity) =>
          val newChildren = children map computeNormalForm
          val simp = reduce(newChildren, polarity)
          simp match {
            case conj: SimpleAnd if checkForContradiction(conj) => SimpleLiteral(!polarity)
            case _ => simp
          }

        case e: SimpleApplication if e.polarity => reuseApplication(e, computeNormalForm(e.f), computeNormalForm(e.arg))

        case SimpleBoundVariable(no, sort, true) => e

        case SimpleVariable(id, sort, true) => e

        case SimpleConstant(id, sort, true) => e

        case SimpleEquality(left, right, true) =>
          val l = computeNormalForm(left)
          val r = computeNormalForm(right)
          if (latticesEQUnchecked(l, r)) SimpleLiteral(true)
          else if (l.uniqueKey >= r.uniqueKey) SimpleEquality(l, r, true)
          else SimpleEquality(r, l, true)

        case SimpleForall(id, body, true) =>
          val inner = computeNormalForm(body)
          if (inner == SimpleLiteral(true)) SimpleLiteral(true)
          else if (inner == SimpleLiteral(false)) SimpleLiteral(false)
          else SimpleForall(id, inner, true)

        case e: SimpleLambda => reuseLambda(e, computeNormalForm(e.body))

        case SimpleLiteral(polarity) => e

        case _ => getInversePolar(computeNormalForm(getInversePolar(e)))

        }
        e.normalForm = Some(r)
        r
  }

  /**
   * Returns true if the children of `f` contains a direct contradiction.
   */
  private[kernel] def checkForContradiction(f: SimpleAnd): Boolean = {
    f match {
      case SimpleAnd(children, false) =>
        children.exists(cc => latticesLEQUnchecked(cc, f))
      case SimpleAnd(children, true) =>
        val shadowChildren = children map getInversePolar
        shadowChildren.exists(sc => latticesLEQUnchecked(f, sc))
    }
  }

  /** Checks a positive conjunction represented by two existing sequences without joining or wrapping them. */
  private def conjunctionLEQ(first: Seq[SimpleExpression], second: Seq[SimpleExpression], right: SimpleExpression): Boolean =
    right match
      case SimpleLiteral(true) => true
      case SimpleAnd(children, true) =>
        children.forall(conjunctionLEQ(first, second, _))
      case SimpleAnd(children, false) =>
        first.exists(latticesLEQUnchecked(_, right)) ||
          second.exists(latticesLEQUnchecked(_, right)) ||
          children.exists(child => conjunctionLEQ(first, second, getInversePolar(child)))
      case _ =>
        first.exists(latticesLEQUnchecked(_, right)) || second.exists(latticesLEQUnchecked(_, right))

  /**
   * Reduces a conjunction to an antichain
   */
  private[kernel] def reduceList(children: Seq[SimpleExpression], polarity: Boolean): List[SimpleExpression] = {
    val nonSimplified = SimpleAnd(children, polarity)
    var remaining: Seq[SimpleExpression] = Nil
    def treatChild(i: SimpleExpression): Seq[SimpleExpression] = {
      val r: Seq[SimpleExpression] = i match {
        case SimpleAnd(ch, true) => ch.flatMap(treatChild)
        case SimpleAnd(ch, false) =>
          if (polarity) {
            val trCh = ch map getInversePolar
            trCh.find(f => latticesLEQUnchecked(nonSimplified, f)) match {
              case Some(value) => treatChild(value)
              case None => List(i)
            }
          } else {
            val trCH = ch
            trCH.find(f => latticesLEQUnchecked(f, nonSimplified)) match {
              case Some(value) => treatChild(getInversePolar(value))
              case None => List(i)
            }
          }
        case _ => List(i)
      }
      r
    }
    children.foreach(i => {
      val r = treatChild(i)
      remaining = r ++ remaining
    })

    var accepted: List[SimpleExpression] = Nil
    while (remaining.nonEmpty) {
      val current = remaining.head
      remaining = remaining.tail
      if (!conjunctionLEQ(remaining, accepted, current)) {
        accepted = current :: accepted
      }
    }
    accepted
  }

  /**
   * Reduces a conjunction to a simplified form  using [[reduceList]]
   */
  private[kernel] def reduce(children: Seq[SimpleExpression], polarity: Boolean): SimpleExpression = {
    val accepted: List[SimpleExpression] = reduceList(children, polarity)
    if (accepted.isEmpty) SimpleLiteral(polarity)
    else if (accepted.size == 1)
      if (polarity) accepted.head
      else getInversePolar(accepted.head)
    else SimpleAnd(accepted, polarity)
  }

  /**
   * Checks if `e1` is less than `e2` by the laws of OL
   */
  private[kernel] def latticesLEQ(e1: SimpleExpression, e2: SimpleExpression): Boolean = {
    require(e1.sort == Prop && e2.sort == Prop)
    latticesLEQUnchecked(e1, e2)
  }

  /** Recursive OL containment after callers have established propositional sorts. */
  private def latticesLEQUnchecked(e1: SimpleExpression, e2: SimpleExpression): Boolean = {
    if (e1.uniqueKey == e2.uniqueKey) true
    else
      (e1, e2) match {
        case (SimpleLiteral(false), _) => true

        case (_, SimpleLiteral(true)) => true

        case (SimpleEquality(l1, r1, pol1), SimpleEquality(l2, r2, pol2)) =>
          pol1 == pol2 &&
            ((latticesEQUnchecked(l1, l2) && latticesEQUnchecked(r1, r2)) ||
              (latticesEQUnchecked(l1, r2) && latticesEQUnchecked(r1, l2)))

        case (SimpleForall(x1, body1, polarity1), SimpleForall(x2, body2, polarity2)) =>
          polarity1 == polarity2 && (if (polarity1) latticesLEQUnchecked(body1, body2) else latticesLEQUnchecked(body2, body1))

        // Usual lattice conjunction/disjunction cases
        case (_, SimpleAnd(children, true)) =>
          children.forall(c => latticesLEQUnchecked(e1, c))
        case (SimpleAnd(children, false), _) =>
          children.forall(c => latticesLEQUnchecked(getInversePolar(c), e2))
        case (SimpleAnd(children1, true), SimpleAnd(children2, false)) =>
          children1.exists(c => latticesLEQUnchecked(c, e2)) || children2.exists(c => latticesLEQUnchecked(e1, getInversePolar(c)))
        case (_, SimpleAnd(children, false)) =>
          children.exists(c => latticesLEQUnchecked(e1, getInversePolar(c)))
        case (SimpleAnd(children, true), _) =>
          children.exists(c => latticesLEQUnchecked(c, e2))

        case (s1: SimpleBoundVariable, s2: SimpleBoundVariable) => s1 == s2

        case (s1: SimpleVariable, s2: SimpleVariable) => s1 == s2

        case (s1: SimpleConstant, s2: SimpleConstant) => s1 == s2

        case (SimpleApplication(f1, arg1, polarity1), SimpleApplication(f2, arg2, polarity2)) =>
          polarity1 == polarity2 && latticesEQUnchecked(f1, f2) && latticesEQUnchecked(arg1, arg2)

        case (_, _) => false
      }

  }

  /**
   * Checks if `e1` is equivalent to `e2` by the laws of OL
   */
  private[kernel] def latticesEQ(e1: SimpleExpression, e2: SimpleExpression): Boolean =
    if (e1.uniqueKey == e2.uniqueKey) true
    else if (e1.sort == Prop) latticesLEQ(e1, e2) && latticesLEQ(e2, e1)
    else latticesEQUnchecked(e1, e2)

  /** Recursive OL equality over already well-sorted subexpressions. */
  private def latticesEQUnchecked(e1: SimpleExpression, e2: SimpleExpression): Boolean =
    if (e1.uniqueKey == e2.uniqueKey) true
    else if (e1.sort == Prop) latticesLEQUnchecked(e1, e2) && latticesLEQUnchecked(e2, e1)
    else
      (e1, e2) match {
        case (s1: SimpleBoundVariable, s2: SimpleBoundVariable) => s1 == s2
        case (s1: SimpleVariable, s2: SimpleVariable) => s1 == s2
        case (s1: SimpleConstant, s2: SimpleConstant) => s1 == s2
        case (SimpleApplication(f1, arg1, polarity1), SimpleApplication(f2, arg2, polarity2)) =>
          polarity1 == polarity2 && latticesEQUnchecked(f1, f2) && latticesEQUnchecked(arg1, arg2)
        case (SimpleLambda(x1, body1), SimpleLambda(x2, body2)) =>
          latticesEQUnchecked(body1, body2)
        case (_, _) => false
      }
}
