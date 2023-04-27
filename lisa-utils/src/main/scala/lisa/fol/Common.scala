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

  case class SubstitutionPair[S <: LisaObject[S]](from:SchematicLabel[S], to:S)
  given[S <: LisaObject[S]]: Conversion[(SchematicLabel[S], S), SubstitutionPair[S]] = p => SubstitutionPair[S](p._1, p._2)
  trait Substitution extends Map[SchematicLabel[LisaObject[?]], LisaObject[?]] {
  }
  object Substitution {
    def apply(subst:SubstitutionPair[?]*):Substitution = Map(subst.map(_.productIterator)*).asInstanceOf
  }*/



  sealed trait LisaObject[+T<: LisaObject[T]]{
    this: T =>
    inline def lift:T & this.type = this


    //def substitute[S <: LisaObject[S]](subst:SubstitutionPair[?]*):T
    def substitute[S <: LisaObject[S]](v: SchematicLabel[S], arg: S):T
    //def substitute[S <: LisaObject[S]](v:S, arg:S):Option[T]
    def freeSchematicLabels:Set[SchematicLabel[?]]
    def allSchematicLabels:Set[SchematicLabel[?]]
  }

  /*
  extension[I, O <: LisaObject[O]] (lo: LisaObject[I |-> O]){
    def apply(arg: I): O = lo.asInstanceOf[|->[I, O]].app(arg)
  }*/

  sealed trait TermOrFormula extends LisaObject[TermOrFormula]
  @showAsInfix
  trait |->[-I, +O <: LisaObject[O]] extends /*(I => O) with*/ LisaObject[I|->O] {
    def app(arg: I): O

    def apply(arg: I): O = app(arg)

  }

  trait Label[+A <: LisaObject[A]]{
    this : A =>
    val underlyingLabel: FOL.Label
    val id: FOL.Identifier

    def rename(newid: FOL.Identifier):Label[A]
  }
  sealed trait SchematicLabel[+A <: LisaObject[A]] extends LisaObject[A] with Label[A]{
    this : A =>
    //def get:A = this
    override val underlyingLabel : FOL.SchematicLabel
    def rename(newid: FOL.Identifier):SchematicLabel[A]
  }
  sealed trait ConstantLabel[A <: LisaObject[A]]  extends LisaObject[A] with Label[A] {
    this : A =>
    override val underlyingLabel : FOL.ConstantLabel
    def rename(newid: FOL.Identifier):ConstantLabel[A]
  }

  class TypeError extends Error

  trait Absolute



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

  case class Variable(id: FOL.Identifier) extends Term with Absolute with SchematicLabel[Term] with LisaObject[Term] {
    val underlyingLabel: FOL.VariableLabel = FOL.VariableLabel(id)
    val underlying = FOL.VariableTerm(underlyingLabel)

    @nowarn("msg=Unreachable")
    def substitute[S <: LisaObject[S]](v: SchematicLabel[S], arg: S): Term & (this.type|arg.type) =
      arg match {
        case a: (Term & arg.type) => if (v == this) a.lift else this.lift
        case  _ => this
      }

    def freeSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def rename(newid: FOL.Identifier):Variable = Variable(newid)
    //def substituteTermUnsafe(v: Variable, t: Term): Common.this.Term = ???
    //override def substituteUnsafe(v: Variable, t: Term): Term = if (v.id == id) t else this
    //def substituteUnsafe(v: Variable, t: Term): Term = if (v.id == id) t else this


  }

  case class Constant(id: FOL.Identifier) extends Term with Absolute with ConstantLabel[Constant] {
    val underlyingLabel: FOL.ConstantFunctionLabel = FOL.ConstantFunctionLabel(id, 0)
    val underlying = FOL.Term(underlyingLabel, Seq())

    def substitute[S <: LisaObject[S]](v: SchematicLabel[S], arg: S):Constant & (this.type|arg.type) = this
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def rename(newid: FOL.Identifier):Constant = Constant(newid)

    //def substitute[S <: Common.this.LisaObject[?], I <:Common.this.SchematicLabel[S]] (v: I, arg: S): LisaObject[Common.this.Term] = ???
  }

  //class Truc extends Constant(???) with LisaObject[Constant]

  sealed trait FunctionalLabel[N <: Arity : ValueOf] extends ((Term ** N) |-> Term) with WithArity[N] with Absolute {
    val arity = valueOf[N]
    val id: FOL.Identifier
    val underlyingLabel: FOL.TermLabel
    def substitute[S <: LisaObject[S]](v: SchematicLabel[S], arg: S): ((Term ** N) |-> Term)  & ((this.type & FunctionalLabel[N])|arg.type)

    def app(args: Term ** N): AppliedTerm[N] = AppliedTerm[N](this, args)
    def rename(newid: FOL.Identifier):FunctionalLabel[N]

  }



  case class SchematicFunctionalLabel[N <: Arity : ValueOf](id: FOL.Identifier) extends FunctionalLabel[N] with SchematicLabel[((Term ** N) |-> Term)]{
    val underlyingLabel: FOL.SchematicFunctionLabel = FOL.SchematicFunctionLabel(id, arity)

    @nowarn
    def substitute[S <: LisaObject[S]](v: SchematicLabel[S], arg: S): ((Term ** N) |-> Term)  & (this.type|arg.type) = {
      arg match {
        case a: (((Term ** N) |-> Term) & arg.type) => if (v == this) a.lift else this
        case _ => this
      }
    }
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def rename(newid: FOL.Identifier):SchematicFunctionalLabel[N] = SchematicFunctionalLabel(newid)
  }

  case class ConstantFunctionalLabel[N <: Arity : ValueOf](id: FOL.Identifier) extends FunctionalLabel[N] with ConstantLabel[((Term ** N) |-> Term)]{
    val underlyingLabel: FOL.ConstantFunctionLabel = FOL.ConstantFunctionLabel(id, arity)
    inline def substitute[S <: LisaObject[S]](v: SchematicLabel[S], arg: S): this.type =
      this
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def rename(newid: FOL.Identifier):ConstantFunctionalLabel[N] = ConstantFunctionalLabel(newid)
  }

  case class AppliedTerm[N <: Arity : ValueOf](f: FunctionalLabel[N], args: Term ** N) extends Term with Absolute {
    override val underlying = FOL.Term(f.underlyingLabel, args.toSeq.map(_.underlying))
    def substitute[S <: LisaObject[S]](v: SchematicLabel[S], arg: S):Term = {
      f.substitute(v, arg)(
        args.map[[t]=>>LisaObject[Term]]([u] => (x:u) => x.asInstanceOf[Term].substitute(v, arg)).asInstanceOf
      )
    }

    def freeSchematicLabels:Set[SchematicLabel[?]] = f.freeSchematicLabels ++ args.toSeq.flatMap(_.freeSchematicLabels)
    def allSchematicLabels:Set[SchematicLabel[?]] = f.allSchematicLabels ++ args.toSeq.flatMap(_.allSchematicLabels)
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


  case class VariableFormula(id: FOL.Identifier) extends Formula with Absolute with SchematicLabel[Formula] {
    val underlyingLabel: FOL.VariableFormulaLabel = FOL.VariableFormulaLabel(id)
    val underlying = FOL.PredicateFormula(underlyingLabel, Seq())

    @nowarn("msg=Unreachable")
    def substitute[S <: LisaObject[S]](v: SchematicLabel[S], arg: S): Formula & (this.type|arg.type) =
      arg match {
        case arg: (Formula & arg.type) => if (v == this) arg.lift else this
        case  _ => throw new TypeError
      }
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def rename(newid: FOL.Identifier):VariableFormula = VariableFormula(newid)
  }

  case class ConstantFormula(id: FOL.Identifier) extends Formula with Absolute with ConstantLabel[Formula] {
    val underlyingLabel: FOL.ConstantPredicateLabel = FOL.ConstantPredicateLabel(id, 0)
    val underlying = FOL.PredicateFormula(underlyingLabel, Seq())

    def substitute[S <: LisaObject[S]](v: SchematicLabel[S], arg: S):this.type = this
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def rename(newid: FOL.Identifier):ConstantFormula = ConstantFormula(newid)
  }

  sealed trait PredicateLabel[N <: Arity : ValueOf] extends |->[Term ** N, Formula] with WithArity[N] with Absolute {
    val arity = valueOf[N]
    val id: FOL.Identifier
    val underlyingLabel: FOL.PredicateLabel

    def app(args: Term ** N): AppliedPredicate[N] = AppliedPredicate[N](this, args)
    def rename(newid: FOL.Identifier):PredicateLabel[N]
  }

  case class SchematicPredicateLabel[N <: Arity : ValueOf](id: FOL.Identifier) extends PredicateLabel[N] with SchematicLabel[Term ** N |->Formula]{
    val underlyingLabel: FOL.SchematicPredicateLabel = FOL.SchematicPredicateLabel(id, arity)

    @nowarn
    def substitute[S <: LisaObject[S]](v: SchematicLabel[S], arg: S): |->[Term ** N, Formula]  & (this.type|arg.type) = {
      arg match {
        case arg: (|->[Term ** N, Formula]  & arg.type) => if (v == this) arg.lift else this
        case _ => this
      }
    }
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def rename(newid: FOL.Identifier):SchematicPredicateLabel[N] = SchematicPredicateLabel(newid)

  }

  case class ConstantPredicateLabel[N <: Arity : ValueOf](id: FOL.Identifier) extends PredicateLabel[N] with ConstantLabel[Term ** N |->Formula]{
    val underlyingLabel: FOL.ConstantPredicateLabel = FOL.ConstantPredicateLabel(id, arity)
    inline def substitute[S <: LisaObject[S]](v: SchematicLabel[S], arg: S): this.type =
      this
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def rename(newid: FOL.Identifier):ConstantPredicateLabel[N] = ConstantPredicateLabel(newid)
  }

  case class AppliedPredicate[N <: Arity : ValueOf](p: PredicateLabel[N], args: Term ** N) extends Formula with Absolute {
    override val underlying = FOL.PredicateFormula(p.underlyingLabel, args.toSeq.map(_.underlying))
    def substitute[S <: LisaObject[S]](v: SchematicLabel[S], arg: S):Formula = p.substitute(v, arg)(
      args.map[[t]=>>LisaObject[Term]]([u] => (x:u) => x.asInstanceOf[Term].substitute(v, arg)).asInstanceOf
    )

    def freeSchematicLabels:Set[SchematicLabel[?]] = p.freeSchematicLabels ++ args.toSeq.flatMap(_.freeSchematicLabels)
    def allSchematicLabels:Set[SchematicLabel[?]] = p.allSchematicLabels ++ args.toSeq.flatMap(_.allSchematicLabels)
    //override def substituteUnsafe(v: Variable, subs: Term) = AppliedPredicateFormula[N](f, args.map(_.substituteUnsafe(v, subs)))
  }


  sealed trait ConnectorLabel[N <: Arity : ValueOf] extends |->[Formula ** N, Formula] with WithArity[N] with Absolute {
    val arity = valueOf[N]
    val id: FOL.Identifier
    val underlyingLabel: FOL.ConnectorLabel

    def app(args: Formula ** N): AppliedConnector[N] = AppliedConnector[N](this, args)
    def rename(newid: FOL.Identifier):ConnectorLabel[N]
  }

  case class SchematicConnectorLabel[N <: Arity : ValueOf](id: FOL.Identifier) extends ConnectorLabel[N] with SchematicLabel[Formula ** N |->Formula]{
    val underlyingLabel: FOL.SchematicConnectorLabel = FOL.SchematicConnectorLabel(id, arity)

    @nowarn
    def substitute[S <: LisaObject[S]](v: SchematicLabel[S], arg: S): |->[Formula ** N, Formula]  & (this.type|arg.type) = {
      arg match {
        case arg: (|->[Formula ** N, Formula] & arg.type) => if (v == this) arg.lift else this
        case _ => this
      }
    }
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def rename(newid: FOL.Identifier):SchematicConnectorLabel[N] = SchematicConnectorLabel(newid)

  }
/*
  case class ConstantPredicateLabel[N <: Arity : ValueOf](id: FOL.Identifier) extends PredicateLabel[N] with ConstantLabel[Term ** N |->Formula]{
    val underlyingLabel: FOL.ConstantPredicateLabel = FOL.ConstantPredicateLabel(id, arity)
    inline def substitute[S <: LisaObject[S]](v: SchematicLabel[S], arg: S): this.type =
      this
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def rename(newid: FOL.Identifier):ConstantPredicateLabel[N] = ConstantPredicateLabel(newid)
  }
*/
  case class AppliedConnector[N <: Arity : ValueOf](p: ConnectorLabel[N], args: Formula ** N) extends Formula with Absolute {
    override val underlying = FOL.ConnectorFormula(p.underlyingLabel, args.toSeq.map(_.underlying))
    def substitute[S <: LisaObject[S]](v: SchematicLabel[S], arg: S):Formula = p.substitute(v, arg)(
      args.map[[t]=>>LisaObject[Formula]]([u] => (x:u) => x.asInstanceOf[Formula].substitute(v, arg)).asInstanceOf
    )

    def freeSchematicLabels:Set[SchematicLabel[?]] = p.freeSchematicLabels ++ args.toSeq.flatMap(_.freeSchematicLabels)
    def allSchematicLabels:Set[SchematicLabel[?]] = p.allSchematicLabels ++ args.toSeq.flatMap(_.allSchematicLabels)
    //override def substituteUnsafe(v: Variable, subs: Term) = AppliedPredicateFormula[N](f, args.map(_.substituteUnsafe(v, subs)))
  }

  /*
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
