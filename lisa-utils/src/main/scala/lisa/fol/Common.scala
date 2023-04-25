package lisa.fol

import lisa.kernel.fol.FOL

import scala.annotation.showAsInfix
import scala.annotation.nowarn
import scala.compiletime.ops.int.-

trait Common {

  type Arity = Int & Singleton

  @showAsInfix
  type **[T, N <: Arity] <: Tuple & Matchable = N match {
    case 0 => EmptyTuple
    case _ => T *: (T ** (N - 1))
  }

  extension[T <: Matchable, N <: Arity] (tup: T ** N) {
    def toSeq: Seq[T] = tup.productIterator.toSeq.asInstanceOf
  }

  trait WithArity[N <: Arity] {
    val arity: N
  }

  def isLegalApplication(withArity: WithArity[?], args: Seq[?]): Boolean =
    withArity.arity == -1 || withArity.arity == args.size

  /*
  //@annotation.implicitNotFound("It can not be proven that ${T} is of type Term, Formula or |->")
  sealed trait Foo[+T]
  given TermFoo: Foo[Term] = new Foo[Term] {}
  given FormulaFoo: Foo[Formula] = new Foo[Formula] {}
  given TermOrFormulaFoo: Foo[TermOrFormula] = new Foo[TermOrFormula] {}
  given FunFoo[I, O <: LisaObject[?]]: Foo[I|->O] = new Foo[I|->O] {}

  sealed trait Bar[+T]
  given FunBar[I, O <: LisaObject[?]]: Bar[I|->O] = new Bar[I|->O] {}
*/
  sealed trait LisaObject[+T<: LisaObject[?]]{
    def substitute[S <: LisaObject[?], I<:SchematicLabel[S]](v:I, arg:S):LisaObject[T]
  }

  extension[I, O <: LisaObject[?]] (lo: LisaObject[I |-> O]){
    def apply(arg: I): O = lo.asInstanceOf[|->[I, O]].app(arg)
  }

  sealed trait TermOrFormula extends LisaObject[TermOrFormula]
  @showAsInfix
  trait |->[-I, +O <: LisaObject[?]] extends /*(I => O) with*/ LisaObject[I|->O] {
    def app(arg: I): O

    def apply(arg: I): O = app(arg)

  }

  trait Label{
    val underlyingLabel: FOL.Label
    val id: FOL.Identifier
  }
  sealed trait SchematicLabel[A <: LisaObject[?]] extends Label{
    override val underlyingLabel : FOL.SchematicLabel
  }
  sealed trait ConstantLabel[TF<:TermOrFormula]  extends Label {
    override val underlyingLabel : FOL.ConstantLabel
  }


  //////////
  // Term //
  //////////


  abstract class Term extends TermOrFormula with LisaObject[Term] {
    val underlying: FOL.Term
/*
    def substituteTermUnsafe(v: Variable, t: Term): Term

    final def substituteTerm(v: Variable, t: Term): Term = {
      val r = substituteTermUnsafe(v, t)
      assert(r.underlying == FOL.substituteVariables(underlying, Map((FOL.VariableLabel(v.id), t.underlying))))
      r
    }*/

  }

  /////////////////////
  // Matching Kernel //
  /////////////////////

  class TypeError extends Error

  trait Absolute



  case class Variable(id: FOL.Identifier) extends Term with Absolute with SchematicLabel[Term] {
    val underlyingLabel: FOL.VariableLabel = FOL.VariableLabel(id)
    val underlying = FOL.VariableTerm(underlyingLabel)

    @nowarn("msg=Unreachable")
    def substitute[S <: LisaObject[?], I <: SchematicLabel[S]](v: I, arg: S): LisaObject[Term] =
      if (v == this) {
        arg match {
          case arg: Term => arg
          case  _ => throw new TypeError
        }
    } else this

    //def substituteTermUnsafe(v: Variable, t: Term): Common.this.Term = ???
    //override def substituteUnsafe(v: Variable, t: Term): Term = if (v.id == id) t else this
    //def substituteUnsafe(v: Variable, t: Term): Term = if (v.id == id) t else this
  }

  case class Constant(id: FOL.Identifier) extends Term with Absolute with ConstantLabel[Term] {
    val underlyingLabel: FOL.ConstantFunctionLabel = FOL.ConstantFunctionLabel(id, 0)
    val underlying = FOL.Term(underlyingLabel, Seq())

    def substitute[S <: LisaObject[?], I<:SchematicLabel[S]](v:I, arg:S):LisaObject[Term] = this


    //def substitute[S <: Common.this.LisaObject[?], I <:Common.this.SchematicLabel[S]] (v: I, arg: S): LisaObject[Common.this.Term] = ???
  }

  sealed trait FunctionalLabel[N <: Arity : ValueOf] extends |->[Term ** N, Term] with WithArity[N] with Absolute {
    val arity = valueOf[N]
    val id: FOL.Identifier
    val underlyingLabel: FOL.TermLabel

    def app(args: Term ** N): AppliedTerm[N] = AppliedTerm[N](this, args.toSeq)
    def substitute[S <: LisaObject[?], I<:SchematicLabel[S]](v:I, arg:S):LisaObject[|->[Term ** N, Term]] =
      if (v==this) {
        arg match {
          case a: |->[Term ** N, Term] => a
          case _ => throw new TypeError
        }
      }
      else
        this
  }

  case class ConstantFunctionalLabel[N <: Arity : ValueOf](id: FOL.Identifier) extends FunctionalLabel[N] with ConstantLabel[Term]{
    val underlyingLabel: FOL.ConstantFunctionLabel = FOL.ConstantFunctionLabel(id, arity)

  }

  case class SchematicFunctionalLabel[N <: Arity : ValueOf](id: FOL.Identifier) extends FunctionalLabel[N] with SchematicLabel[|->[Term ** N, Term]]{
    val underlyingLabel: FOL.SchematicFunctionLabel = FOL.SchematicFunctionLabel(id, arity)

  }

  case class AppliedTerm[N <: Arity : ValueOf](f: FunctionalLabel[N], args: Seq[Term]) extends Term with Absolute {
    require(isLegalApplication(f, args), "The number of arguments does not match the arity")
    override val underlying = FOL.Term(f.underlyingLabel, args.map(_.underlying))
    def substitute[S <: LisaObject[?], I<:SchematicLabel[S]](v:I, arg:S):LisaObject[Term] = ???

    //override def substituteUnsafe(v: Variable, subs: Term) = AppliedTerm[N](f, args.map(_.substituteUnsafe(v, subs)))
  }


  //////////////
  // Formulas //
  //////////////


  abstract class Formula extends TermOrFormula with LisaObject[Formula] {
    val underlying: FOL.Formula

    /*
    def substituteUnsafe(v: Variable, t: Term): Formula

    final def substitute(v: Variable, t: Term): Formula = {
      val r = substituteUnsafe(v, t)
      assert(r.underlying == FOL.substituteVariables(underlying, Map((FOL.VariableLabel(v.id), t.underlying))))
      r
    }*/

  }
  /*

  case class VariableFormula(id: FOL.Identifier) extends Formula with Absolute with SchematicLabel[Formula] {
    val underlyingLabel: FOL.VariableFormulaLabel = FOL.VariableFormulaLabel(id)
    val underlying = FOL.PredicateFormula(underlyingLabel, Seq())

    //override def substituteUnsafe(v: Variable, t: Term): Formula = this
  }

  case class ConstantFormula(id: FOL.Identifier) extends Formula with Absolute with ConstantLabel[Formula] {
    val underlyingLabel: FOL.ConstantPredicateLabel = FOL.ConstantPredicateLabel(id, 0)
    val underlying = FOL.PredicateFormula(underlyingLabel, Seq())

    //override def substituteUnsafe(v: Variable, t: Term): Formula = this
  }

  sealed trait PredicateLabel[N <: Arity : ValueOf] extends |->[Term ** N, Formula] with WithArity[N] with Absolute {
    val arity = valueOf[N]
    val id: FOL.Identifier
    val underlyingLabel: FOL.PredicateLabel

    def app(args: Term ** N): AppliedPredicateFormula[N] = AppliedPredicateFormula[N](this, args.toSeq)
  }

  case class ConstantPredicateLabel[N <: Arity : ValueOf](id: FOL.Identifier) extends PredicateLabel[N] with ConstantLabel[Formula]{
    val underlyingLabel: FOL.ConstantPredicateLabel = FOL.ConstantPredicateLabel(id, arity)

  }

  case class SchematicPredicateLabel[N <: Arity : ValueOf](id: FOL.Identifier) extends PredicateLabel[N] with SchematicLabel[Formula]{
    val underlyingLabel: FOL.SchematicPredicateLabel = FOL.SchematicPredicateLabel(id, arity)

  }

  case class AppliedPredicateFormula[N <: Arity : ValueOf](f: PredicateLabel[N], args: Seq[Term]) extends Formula with Absolute {
    require(isLegalApplication(f, args), "The number of arguments does not match the arity")
    override val underlying = FOL.PredicateFormula(f.underlyingLabel, args.map(_.underlying))

    //override def substituteUnsafe(v: Variable, subs: Term) = AppliedPredicateFormula[N](f, args.map(_.substituteUnsafe(v, subs)))
  }


  trait ConnectorLabel[N <: Arity : ValueOf] extends |->[Formula ** N, Formula] with WithArity[N] with Absolute {
    val arity = valueOf[N]
    val id: FOL.Identifier
    val underlyingLabel: FOL.ConnectorLabel

    def app(args: Formula ** N): AppliedConnectorFormula[N] = AppliedConnectorFormula[N](this, args.toSeq)
  }

  sealed abstract class ConstantConnectorLabel[N <: Arity : ValueOf] extends ConnectorLabel[N] with ConstantLabel[Formula]{
    val id: FOL.Identifier
    val underlyingLabel: FOL.ConstantConnectorLabel
  }

  case object Neg extends ConstantConnectorLabel[1] {
    val id: FOL.Identifier = FOL.Identifier("¬")
    val underlyingLabel: FOL.Neg.type = FOL.Neg
  }

  case object Implies extends ConstantConnectorLabel[2] {
    val id: FOL.Identifier = FOL.Identifier("⇒")
    val underlyingLabel: FOL.Implies.type = FOL.Implies
  }

  case object Iff extends ConstantConnectorLabel[2] {
    val id: FOL.Identifier = FOL.Identifier("⇔")
    val underlyingLabel: FOL.Iff.type = FOL.Iff
  }

  case object And extends ConstantConnectorLabel[-1] {
    val id: FOL.Identifier = FOL.Identifier("∧")
    val underlyingLabel: FOL.And.type = FOL.And
  }

  case object Or extends ConstantConnectorLabel[-1] {
    val id: FOL.Identifier = FOL.Identifier("∨")
    val underlyingLabel: FOL.Or.type = FOL.Or
  }


  case class SchematicConnectorLabel[N <: Arity : ValueOf](id: FOL.Identifier) extends ConnectorLabel[N] with SchematicLabel[Formula]{
    val underlyingLabel: FOL.SchematicConnectorLabel = FOL.SchematicConnectorLabel(id, arity)

  }

  case class AppliedConnectorFormula[N <: Arity : ValueOf](f: ConnectorLabel[N], args: Seq[Formula]) extends Formula with Absolute {
    require(isLegalApplication(f, args), "The number of arguments does not match the arity")
    override val underlying = FOL.ConnectorFormula(f.underlyingLabel, args.map(_.underlying))

    //override def substituteUnsafe(v: Variable, subs: Term) = AppliedConnectorFormula[N](f, args.map(_.substituteUnsafe(v, subs)))
  }


  abstract class BinderLabel extends |->[(Variable, Formula), Formula] with Absolute {
    val id: FOL.Identifier
  }

  trait BaseBinderLabel extends BinderLabel {
    val underlyingLabel: FOL.BinderLabel

    def app(arg: (Variable, Formula)): Formula = BaseQuantifiedFormula(this, arg._1, arg._2)

  }

  case object Forall extends BaseBinderLabel {
    val id = FOL.Identifier("∀")
    val underlyingLabel: FOL.Forall.type = FOL.Forall
  }


  case object Exists extends BaseBinderLabel {
    val id = FOL.Identifier("∃")
    val underlyingLabel: FOL.Exists.type = FOL.Exists
  }


  case object ExistsOne extends BaseBinderLabel {
    val id = FOL.Identifier("∃!")
    val underlyingLabel: FOL.ExistsOne.type = FOL.ExistsOne
  }

  case class BaseQuantifiedFormula(f: BaseBinderLabel, x: Variable, inner: Formula) extends Formula with Absolute {
    override val underlying = FOL.BinderFormula(f.underlyingLabel, x.underlyingLabel, inner.underlying)

    /*
    override def substituteUnsafe(v: Variable, subs: Term) = {
      if (v == x)
        this
      else
        BaseQuantifiedFormula(f, x, inner.substituteUnsafe(v, subs))
    }

     */
  }


   */

}
