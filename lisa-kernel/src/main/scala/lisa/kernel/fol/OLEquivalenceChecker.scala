package lisa.kernel.fol

import scala.collection.mutable
import lisa.kernel.fol.Syntax

private[fol] trait OLEquivalenceChecker extends Syntax {


  def reducedForm(expr: Expression): Expression = {
    val p = simplify(expr)
    val nf = computeNormalForm(p)
    val fln = fromLocallyNameless(nf, Map.empty, 0)
    val res = toExpressionAIG(fln)
    res
  }

  def reducedNNFForm(formula: Expression): Expression = {
    val p = simplify(formula)
    val nf = computeNormalForm(p)
    val fln = fromLocallyNameless(nf, Map.empty, 0)
    val res = toExpressionNNF(fln, true)
    res
  }
  def reduceSet(s: Set[Expression]): Set[Expression] = {
    var res: List[Expression] = Nil
    s.map(reducedForm)
      .foreach({ f =>
        if (!res.exists(isSame(f, _))) res = f :: res
      })
    res.toSet
  }

  @deprecated("Use isSame instead", "0.8")
  def isSameTerm(term1: Expression, term2: Expression): Boolean = isSame(term1, term2)
  def isSame(e1: Expression, e2: Expression): Boolean = {
    val nf1 = computeNormalForm(simplify(e1))
    val nf2 = computeNormalForm(simplify(e2))
    latticesEQ(nf1, nf2)
    
  }

  /**
   * returns true if the first argument implies the second by the laws of ortholattices.
   */
  def isImplying(e1: Expression, e2: Expression): Boolean = {
    require(e1.sort == Formula && e2.sort == Formula) 
    val nf1 = computeNormalForm(simplify(e1))
    val nf2 = computeNormalForm(simplify(e2))
    latticesLEQ(nf1, nf2)
  }

  def isSubset(s1: Set[Expression], s2: Set[Expression]): Boolean = {
    s1.forall(e1 => s2.exists(e2 => isSame(e1, e2)))
  }
  def isSameSet(s1: Set[Expression], s2: Set[Expression]): Boolean =
    isSubset(s1, s2) && isSubset(s2, s1)

  def isSameSetL(s1: Set[Expression], s2: Set[Expression]): Boolean =
    isSame(s1.reduceLeft(and(_)(_)), s2.reduceLeft(and(_)(_)))

  def isSameSetR(s1: Set[Expression], s2: Set[Expression]): Boolean =
    isSame(s1.reduceLeft(or(_)(_)), s2.reduceLeft(or(_)(_)))

  def contains(s: Set[Expression], f: Expression): Boolean = {
    s.exists(g => isSame(f, g))
  }


  private var totSimpleExpr = 0
  sealed abstract class SimpleExpression {
    val sort: Sort
    val containsFormulas : Boolean

    val uniqueKey = totSimpleExpr
    totSimpleExpr += 1
    val size : Int //number of subterms which are actual concrete formulas
    private[OLEquivalenceChecker] var inverse : Option[SimpleExpression] = None
    def getInverse = inverse
    private[OLEquivalenceChecker] var NNF_pos: Option[Expression] = None
    def getNNF_pos = NNF_pos
    private[OLEquivalenceChecker] var NNF_neg: Option[Expression] = None
    def getNNF_neg = NNF_neg
    private[OLEquivalenceChecker] var formulaAIG: Option[Expression] = None
    def getFormulaAIG = formulaAIG
    private[OLEquivalenceChecker] var normalForm: Option[SimpleExpression] = if (containsFormulas) None else Some(this)
      def getNormalForm = normalForm

    // caching for lessThan
    private val lessThanBitSet: mutable.Set[Long] = new mutable.HashSet()
    setLessThanCache(this, true)

    def lessThanCached(other: SimpleExpression): Option[Boolean] = {
      val otherIx = 2 * other.uniqueKey
      if (lessThanBitSet.contains(otherIx)) Some(lessThanBitSet.contains(otherIx + 1))
      else None
    }

    def setLessThanCache(other: SimpleExpression, value: Boolean): Unit = {
      val otherIx = 2 * other.uniqueKey
      lessThanBitSet.contains(otherIx)
      if (value) lessThanBitSet.update(otherIx + 1, true)
    }
  }

  case class SimpleVariable(id: Identifier, sort:Sort, polarity: Boolean) extends SimpleExpression {
    val containsFormulas: Boolean = sort == Formula
    val size = 1
  }
  case class SimpleBoundVariable(no: Int, sort: Sort, polarity: Boolean) extends SimpleExpression {
    val containsFormulas: Boolean = sort == Formula
    val size = 1
  }
  case class SimpleConstant(id: Identifier, sort: Sort, polarity: Boolean) extends SimpleExpression {
    val containsFormulas: Boolean = sort == Formula
    val size = 1
  }
  case class SimpleApplication(f: SimpleExpression, arg: SimpleExpression, polarity: Boolean) extends SimpleExpression {
    private val legalapp = legalApplication(f.sort, arg.sort) // Optimize after debugging
    val sort = legalapp.get
    val containsFormulas: Boolean = sort == Formula || f.containsFormulas || arg.containsFormulas
    val size = f.size + arg.size
  }
  case class SimpleLambda(v: Variable, body: SimpleExpression) extends SimpleExpression {
    val containsFormulas: Boolean = body.containsFormulas
    val sort = (v.sort -> body.sort)
    val size = body.size
  }
  case class SimpleAnd(children: Seq[SimpleExpression], polarity: Boolean) extends SimpleExpression{
    val containsFormulas: Boolean = true
    val sort = Formula
    val size = children.map(_.size).sum+1
  }
  case class SimpleForall(id: Identifier, body: SimpleExpression, polarity: Boolean) extends SimpleExpression {
    val containsFormulas: Boolean = true
    val sort = Formula
    val size = body.size +1
  }
  case class SimpleLiteral(polarity: Boolean) extends SimpleExpression {
    val containsFormulas: Boolean = true
    val sort = Formula
    val size = 1
  }
  case class SimpleEquality(left: SimpleExpression, right: SimpleExpression, polarity: Boolean) extends SimpleExpression {
    val containsFormulas: Boolean = true
    val sort = Formula
    val size = left.size + right.size + 1
  }


  def getInversePolar(e: SimpleExpression): SimpleExpression = e.inverse match {
    case Some(inverse) => inverse
    case None => 
      val inverse = e match {
        case e: SimpleAnd => e.copy(polarity = !e.polarity)
        case e: SimpleForall => e.copy(polarity = !e.polarity)
        case e: SimpleLiteral => e.copy(polarity = !e.polarity)
        case e: SimpleEquality => e.copy(polarity = !e.polarity)
        case e: SimpleVariable if e.sort == Formula => e.copy(polarity = !e.polarity)
        case e: SimpleBoundVariable if e.sort == Formula => e.copy(polarity = !e.polarity)
        case e: SimpleConstant if e.sort == Formula => e.copy(polarity = !e.polarity)
        case e: SimpleApplication if e.sort == Formula => e.copy(polarity = !e.polarity)
        case _ => throw new Exception("Cannot invert expression that is not a formula")
      }
      e.inverse = Some(inverse)
      inverse
  }


  def toExpressionAIG(e:SimpleExpression): Expression =
    if (e.formulaAIG.isDefined) e.formulaAIG.get
    else {
      val r: Expression = e match {
        case SimpleAnd(children, polarity) =>
          val f = children.map(toExpressionAIG).reduceLeft(and(_)(_))
          if (polarity) f else neg(f)
        case SimpleForall(x, body, polarity) =>
          val f = forall(Lambda(Variable(x, Term), toExpressionAIG(body)))
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
            g else 
              neg(g)
        case SimpleLambda(v, body) => Lambda(v, toExpressionAIG(body))
      }
      e.formulaAIG = Some(r)
      r
    }

  def toExpressionNNF(e: SimpleExpression, positive: Boolean): Expression = {
    if (positive){
      if (e.NNF_pos.isDefined) return e.NNF_pos.get
      if (e.inverse.isDefined && e.inverse.get.NNF_neg.isDefined) return e.inverse.get.NNF_neg.get
    }
    else if (!positive) {
      if (e.NNF_neg.isDefined) return e.NNF_neg.get
      if (e.inverse.isDefined && e.inverse.get.NNF_pos.isDefined) return e.inverse.get.NNF_pos.get
    }
    val r = e match {
      case SimpleAnd(children, polarity) =>
        if (positive == polarity) 
          children.map(toExpressionNNF(_, true)).reduceLeft(and(_)(_))
        else 
          children.map(toExpressionNNF(_, false)).reduceLeft(or(_)(_))
      case SimpleForall(x, body, polarity) =>
        if (positive == polarity) 
          forall(Lambda(Variable(x, Term), toExpressionNNF(body, true))) //rebuilding variable not ideal
        else 
          exists(Lambda(Variable(x, Term), toExpressionNNF(body, false)))
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
    else  e.NNF_neg = Some(r)
    r
  }



  def polarize(e: Expression, polarity:Boolean): SimpleExpression = e match {
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
        ), polarity)
    case and(arg1, arg2) =>
      SimpleAnd(Seq(polarize(arg1, true), polarize(arg2, true)), polarity)
    case or(arg1, arg2) => 
      SimpleAnd(Seq(polarize(arg1, false), polarize(arg2, false)), !polarity)
    case forall(Lambda(v, body)) =>
      SimpleForall(v.id, polarize(body, true), polarity)
    case exists(Lambda(v, body)) =>
      SimpleForall(v.id, polarize(body, false), !polarity)
    case equality(arg1, arg2) =>
      SimpleEquality(polarize(arg1, true), polarize(arg2, true), polarity)
    case Application(f, arg) => 
      SimpleApplication(polarize(f, true), polarize(arg, true), polarity)
    case Lambda(v, body) => SimpleLambda(v, polarize(body, true))
    case Constant(`top`, Formula) => SimpleLiteral(true)
    case Constant(`bot`, Formula) => SimpleLiteral(false)
    case Constant(id, sort) => SimpleConstant(id, sort, polarity)
    case Variable(id, sort) => SimpleVariable(id, sort, polarity)
  }

  def toLocallyNameless(e: SimpleExpression, subst: Map[(Identifier, Sort), Int], i: Int): SimpleExpression = e match {
    case SimpleAnd(children, polarity) => SimpleAnd(children.map(toLocallyNameless(_, subst, i)), polarity)
    case SimpleForall(x, inner, polarity) => SimpleForall(x, toLocallyNameless(inner, subst + ((x, Term) -> i), i + 1), polarity)
    case e: SimpleLiteral => e
    case SimpleEquality(left, right, polarity) => SimpleEquality(toLocallyNameless(left, subst, i), toLocallyNameless(right, subst, i), polarity)
    case v: SimpleVariable => 
      if (subst.contains((v.id, v.sort))) SimpleBoundVariable(i - subst((v.id, v.sort)), v.sort, v.polarity)
      else v
    case s: SimpleBoundVariable => throw new Exception("This case should be unreachable. Can't call toLocallyNameless on a bound variable")
    case e: SimpleConstant => e
    case SimpleApplication(arg1, arg2, polarity) => SimpleApplication(toLocallyNameless(arg1, subst, i), toLocallyNameless(arg2, subst, i), polarity)
    case SimpleLambda(x, inner) => SimpleLambda(x, toLocallyNameless(inner, subst + ((x.id, x.sort) -> i), i + 1))
  }

  def fromLocallyNameless(e: SimpleExpression, subst: Map[Int, (Identifier, Sort)], i: Int): SimpleExpression = e match {
    case SimpleAnd(children, polarity) => SimpleAnd(children.map(fromLocallyNameless(_, subst, i)), polarity)
    case SimpleForall(x, inner, polarity) => SimpleForall(x, fromLocallyNameless(inner, subst + (i -> (x, Term)), i + 1), polarity)
    case e: SimpleLiteral => e
    case SimpleEquality(left, right, polarity) => SimpleEquality(fromLocallyNameless(left, subst, i), fromLocallyNameless(right, subst, i), polarity)
    case SimpleBoundVariable(no, sort, polarity) => 
      val dist = i - no
      if (subst.contains(dist)) {val (id, sort) = subst(dist); SimpleVariable(id, sort, polarity)}
      else throw new Exception("This case should be unreachable, error")
    case v: SimpleVariable => v
    case e: SimpleConstant => e
    case SimpleApplication(arg1, arg2, polarity) => SimpleApplication(fromLocallyNameless(arg1, subst, i), fromLocallyNameless(arg2, subst, i), polarity)
    case SimpleLambda(x, inner) => SimpleLambda(x, fromLocallyNameless(inner, subst + (i -> (x.id, x.sort)), i + 1))
  }

  def simplify(e: Expression): SimpleExpression = toLocallyNameless(polarize(e, true), Map.empty, 0)


  //////////////////////
  //// OL Algorithm ////
  //////////////////////

  def computeNormalForm(e: SimpleExpression): SimpleExpression = {
    e.normalForm match {
      case Some(value) =>
        value
      case None => 
        val r: SimpleExpression = e match {
          case SimpleAnd(children, polarity) => 
            val newChildren = children map computeNormalForm
            val simp = reduce(newChildren, polarity)
            simp match {
              case conj: SimpleAnd if checkForContradiction(conj) => SimpleLiteral(!polarity)
              case _ => simp
            }

          case SimpleApplication(f, arg, true) => SimpleApplication(computeNormalForm(f), computeNormalForm(arg), true)

          case SimpleBoundVariable(no, sort, true) => e

          case SimpleVariable(id, sort, true) => e

          case SimpleConstant(id, sort, true) => e

          case SimpleEquality(left, right, true) => 
            val l = computeNormalForm(left)
            val r = computeNormalForm(right)
            if (l == r) SimpleLiteral(true)
            else if (l.uniqueKey >= r.uniqueKey) SimpleEquality(l, r, true)
            else SimpleEquality(r, l, true)

          case SimpleForall(id, body, true) => SimpleForall(id, computeNormalForm(body), true)

          case SimpleLambda(v, body) => SimpleLambda(v, computeNormalForm(body))

          case SimpleLiteral(polarity) => e

          case _ => getInversePolar(computeNormalForm(getInversePolar(e)))

        }
        e.normalForm = Some(r)
        r
    }
  }

  def checkForContradiction(f: SimpleAnd): Boolean = {
    f match {
      case SimpleAnd(children, false) =>
        children.exists(cc => latticesLEQ(cc, f))
      case SimpleAnd(children, true) =>
        val shadowChildren = children map getInversePolar
        shadowChildren.exists(sc => latticesLEQ(f, sc))
    }
  }

  def reduceList(children: Seq[SimpleExpression], polarity: Boolean): List[SimpleExpression] = {
    val nonSimplified = SimpleAnd(children, polarity)
    var remaining : Seq[SimpleExpression] = Nil
    def treatChild(i: SimpleExpression): Seq[SimpleExpression] = {
      val r: Seq[SimpleExpression] = i match {
        case SimpleAnd(ch, true) => ch
        case SimpleAnd(ch, false) => 
          if (polarity) {
            val trCh = ch map getInversePolar
            trCh.find(f => latticesLEQ(nonSimplified, f)) match {
              case Some(value) => treatChild(value)
              case None => List(i)
            }
          } else {
            val trCH = ch
            trCH.find(f => latticesLEQ(f, nonSimplified)) match {
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
      if (!latticesLEQ(SimpleAnd(remaining ++ accepted, true), current)) {
        accepted = current :: accepted
      }
    }
    accepted
  }


  def reduce(children: Seq[SimpleExpression], polarity: Boolean): SimpleExpression = {
    val accepted: List[SimpleExpression] = reduceList(children, polarity)
    if (accepted.isEmpty) SimpleLiteral(polarity)
    else if (accepted.size == 1) 
      if (polarity) accepted.head
      else getInversePolar(accepted.head)
    else SimpleAnd(accepted, polarity)
  }

  
  def latticesLEQ(e1: SimpleExpression, e2: SimpleExpression): Boolean = {
    require(e1.sort == Formula && e2.sort == Formula)
    if (e1.uniqueKey == e2.uniqueKey) true
    else
      e1.lessThanCached(e2) match {
        case Some(value) => value
        case None =>
          val r = (e1, e2) match {
            case (SimpleLiteral(false), _) => true
            
            case (_, SimpleLiteral(true)) => true

            case (SimpleEquality(l1, r1, pol1), SimpleEquality(l2, r2, pol2)) =>
              pol1 == pol2 && latticesEQ(l1, l2) && latticesEQ(r1, r2)

            case (SimpleForall(x1, body1, polarity1), SimpleForall(x2, body2, polarity2)) =>
              polarity1 == polarity2 && (if (polarity1) latticesLEQ(body1, body2) else latticesLEQ(body2, body1))

            // Usual lattice conjunction/disjunction cases
            case (_, SimpleAnd(children, true)) =>
              children.forall(c => latticesLEQ(e1, c))
            case (SimpleAnd(children, false), _) =>
              children.forall(c => latticesLEQ(getInversePolar(c), e2))
            case (SimpleAnd(children1, true), SimpleAnd(children2, false)) =>
              children1.exists(c => latticesLEQ(c, e2)) || children2.exists(c => latticesLEQ(e1, getInversePolar(c)))
            case (_, SimpleAnd(children, false)) =>
              children.exists(c => latticesLEQ(e1, getInversePolar(c)))
            case (SimpleAnd(children, true), _) =>
              children.exists(c => latticesLEQ(c, e2))


            case (s1: SimpleBoundVariable, s2: SimpleBoundVariable) => s1 == s2

            case (s1: SimpleVariable, s2: SimpleVariable) => s1 == s2

            case (s1: SimpleConstant, s2: SimpleConstant) => s1 == s2

            case (SimpleApplication(f1, arg1, polarity1), SimpleApplication(f2, arg2, polarity2)) =>
              polarity1 == polarity2 && latticesEQ(f1, f2) && latticesEQ(arg1, arg2)
            
            case (_, _) => false
          }
          e1.setLessThanCache(e2, r)
          r
        }


  }

  def latticesEQ(e1: SimpleExpression, e2: SimpleExpression): Boolean = 
    if (e1.uniqueKey == e2.uniqueKey) true
    else if (e1.sort == Formula) latticesLEQ(e1, e2) && latticesLEQ(e2, e1)
    else (e1, e2) match {
      case (s1: SimpleBoundVariable, s2: SimpleBoundVariable) => s1 == s2
      case (s1: SimpleVariable, s2: SimpleVariable) => s1 == s2
      case (s1: SimpleConstant, s2: SimpleConstant) => s1 == s2
      case (SimpleApplication(f1, arg1, polarity1), SimpleApplication(f2, arg2, polarity2)) =>
        polarity1 == polarity2 && latticesEQ(f1, f2) && latticesEQ(arg1, arg2)
      case (SimpleLambda(x1, body1), SimpleLambda(x2, body2)) =>
        latticesEQ(body1, body2)
      case (_, _) => false
    }
}
