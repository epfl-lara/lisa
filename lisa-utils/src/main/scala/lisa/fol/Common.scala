package lisa.fol

import lisa.utils.K
import scala.annotation.showAsInfix
import scala.annotation.nowarn
import scala.compiletime.ops.int.-
import scala.reflect.ClassTag

trait Common {

  type Arity = Int & Singleton

  @showAsInfix
  type ***[T, N <: Arity] <: (Tuple | List[T]) & Matchable = N match {
    case -1 => List[T]
    case 0 => EmptyTuple
    case _ => T *: (T *** (N - 1))
  }
  type **[T, N <: Arity] = Seq[T] | ***[T, N]

  extension[T, N <: Arity] (self: T ** N) {
    @nowarn("msg=checked at runtime")
    @nowarn("msg=match may not be exhaustive")
    def toSeq: Seq[T] = self match {
      case l: Seq[T] => l
      case tup: Tuple => 
        tup.productIterator.toSeq.asInstanceOf[Seq[T]]
    }
    @nowarn("msg=checked at runtime")
    @nowarn("msg=match may not be exhaustive")
    def map[U](f: T => U): U**N = self match {
      case l : Seq[T] => l.map(f).asInstanceOf[(U**(N))]
      case tup : Tuple => tup.map[[t]=>>U]([u] => (x:u) => f(x.asInstanceOf[T])).asInstanceOf
    }
  }


  trait WithArity[N <: Arity] {
    val arity: N
  }

  def isLegalApplication(withArity: WithArity[?], args: Seq[?]): Boolean =
    withArity.arity == -1 || withArity.arity == args.size



  class SubstPair(val _1: SchematicLabel[_], val _2: _1.SubstitutionType) {
    def toTuple = (_1, _2)
  }



  //case class SubstPair[S <: LisaObject[S]](v: SchematicLabel[S], arg: S)
  inline given trsubst[S <: LisaObject[S]]: Conversion[(SchematicLabel[S], S), SubstPair] = s => SubstPair(s._1, s._2)

  trait LisaObject[+T<: LisaObject[T]] {
    this: T =>
      
    inline def lift:T & this.type = this

    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]):T
    def substitute(pairs: SubstPair*):T = {
      substituteUnsafe(Map(pairs.map(s => (s._1, (s._2: LisaObject[_])))*))
    }
    def substituteOne[S <: LisaObject[S]](v: SchematicLabel[S], arg: S):T = substituteUnsafe(Map(v->arg))
    def freeSchematicLabels:Set[SchematicLabel[?]]
    def allSchematicLabels:Set[SchematicLabel[?]]
  }


  sealed trait TermOrFormula extends LisaObject[TermOrFormula] {
  }
  @showAsInfix
  trait |->[-I, +O <: LisaObject[O]] extends /*(I => O) with*/ LisaObject[I|->O] {
    def app(arg: I): O

    def apply(arg: I): O = app(arg)

  }

  trait Label[A <: LisaObject[A]]{
    this : A =>
    def id: K.Identifier
    def rename(newid: K.Identifier):Label[A]
  }
  sealed trait SchematicLabel[A <: LisaObject[A]] extends LisaObject[A] with Label[A]{
    this : A =>
    type SubstitutionType = A
    def rename(newid: K.Identifier):SchematicLabel[A]

    def :=(replacement:A) = SubstPair(this, replacement)

    //infix def ->(arg:A): SubstPair[A] = SubstPair(this, arg)
  }
  sealed trait ConstantLabel[A <: LisaObject[A]]  extends LisaObject[A] with Label[A] {
    this : A =>
    def rename(newid: K.Identifier):ConstantLabel[A]
  }

  class TypeError extends Error

  trait Absolute



  //////////
  // Term //
  //////////


  abstract class Term extends TermOrFormula with LisaObject[Term] {
    val underlying: K.Term
/*
    def substituteTermUnsafe(v: Variable, t: Term): Term

    final def substituteTerm(v: Variable, t: Term): Term = {
      val r = substituteTermUnsafe(v, t)
      assert(r.underlying == K.substituteVariables(underlying, Map((K.VariableLabel(v.id), t.underlying))))
      r
    }*/

  }

  /////////////////////
  // Matching Kernel //
  /////////////////////

  case class Variable(id: K.Identifier) extends Term with Absolute with SchematicLabel[Term] with LisaObject[Term] {
    val underlyingLabel: K.VariableLabel = K.VariableLabel(id)
    val underlying = K.VariableTerm(underlyingLabel)

    @nowarn("msg=Unreachable")
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): Term = {
      map.get(this.asInstanceOf) match {
        case Some(subst) => subst match {
          case s: Term => s
        }
        case None => this
      }
    }

    def freeSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def rename(newid: K.Identifier):Variable = Variable(newid)
    //def substituteTermUnsafe(v: Variable, t: Term): Common.this.Term = ???
    //override def substituteUnsafe(v: Variable, t: Term): Term = if (v.id == id) t else this
    //def substituteUnsafe(v: Variable, t: Term): Term = if (v.id == id) t else this


  }

  case class Constant(id: K.Identifier) extends Term with Absolute with ConstantLabel[Constant] {
    val underlyingLabel: K.ConstantFunctionLabel = K.ConstantFunctionLabel(id, 0)
    val underlying = K.Term(underlyingLabel, Seq())

    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]):Constant = this
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def rename(newid: K.Identifier):Constant = Constant(newid)

    //def substituteUnsafe[S <: Common.this.LisaObject[?], I <:Common.this.SchematicLabel[S]] (v: I, arg: S): LisaObject[Common.this.Term] = ???
  }

  //class Truc extends Constant(???) with LisaObject[Constant]

  sealed trait FunctionalLabel[N <: Arity] extends ((Term ** N) |-> Term) with WithArity[N] with Absolute {
    val arity : N
    def id: K.Identifier
    val underlyingLabel: K.TermLabel
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): ((Term ** N) |-> Term)

    def app(args: Term ** N): AppliedTerm[N] = AppliedTerm[N](this, args.toSeq)
    def rename(newid: K.Identifier):FunctionalLabel[N]

  }



  case class SchematicFunctionalLabel[N <: Arity](id: K.Identifier, arity : N) extends FunctionalLabel[N] with SchematicLabel[(Term ** N) |-> Term]{
    val underlyingLabel: K.SchematicFunctionLabel = K.SchematicFunctionLabel(id, arity)

    @nowarn
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): ((Term ** N) |-> Term) = {
      map.get(this.asInstanceOf) match {
        case Some(subst) => subst match {
          case s: ((Term ** N) |-> Term) => s
        }
        case None => this
      }
    }
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def rename(newid: K.Identifier):SchematicFunctionalLabel[N] = SchematicFunctionalLabel(newid, arity)
  }

  case class ConstantFunctionalLabel[N <: Arity](id: K.Identifier, arity : N) extends FunctionalLabel[N] with ConstantLabel[((Term ** N) |-> Term)]{
    val underlyingLabel: K.ConstantFunctionLabel = K.ConstantFunctionLabel(id, arity)
    inline def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): this.type =
      this
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def rename(newid: K.Identifier):ConstantFunctionalLabel[N] = ConstantFunctionalLabel(newid, arity)
  }

  case class AppliedTerm[N <: Arity](f: FunctionalLabel[N], args: Seq[Term]) extends Term with Absolute {

    override val underlying = K.Term(f.underlyingLabel, args.toSeq.map(_.underlying))
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]):Term = {
      f.substituteUnsafe(map)(
        args.map[Term]((x:Term) => x.substituteUnsafe(map))
      )
    }

    def freeSchematicLabels:Set[SchematicLabel[?]] = f.freeSchematicLabels ++ args.flatMap(_.freeSchematicLabels)
    def allSchematicLabels:Set[SchematicLabel[?]] = f.allSchematicLabels ++ args.flatMap(_.allSchematicLabels)
    //override def substituteUnsafe(v: Variable, subs: Term) = AppliedTerm[N](f, args.map(_.substituteUnsafe(v, subs)))
  }

  //////////////
  // Formulas //
  //////////////


  abstract class Formula extends TermOrFormula with LisaObject[Formula] {
    val underlying: K.Formula

  }


  case class VariableFormula(id: K.Identifier) extends Formula with Absolute with SchematicLabel[Formula] {
    val underlyingLabel: K.VariableFormulaLabel = K.VariableFormulaLabel(id)
    val underlying = K.PredicateFormula(underlyingLabel, Seq())

    @nowarn("msg=Unreachable")
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): Formula = {
      map.get(this.asInstanceOf) match {
        case Some(subst) => subst match {
          case s: Formula => s
        }
        case None => this
      }
    }
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def rename(newid: K.Identifier):VariableFormula = VariableFormula(newid)
  }

  case class ConstantFormula(id: K.Identifier) extends Formula with Absolute with ConstantLabel[Formula] {
    val underlyingLabel: K.ConstantPredicateLabel = K.ConstantPredicateLabel(id, 0)
    val underlying = K.PredicateFormula(underlyingLabel, Seq())

    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]):this.type = this
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def rename(newid: K.Identifier):ConstantFormula = ConstantFormula(newid)
  }

  sealed trait PredicateLabel[N <: Arity] extends |->[Term ** N, Formula] with WithArity[N] with Absolute {
    val arity : N
    def id: K.Identifier
    val underlyingLabel: K.PredicateLabel // | K.LambdaFormulaFormula

    def interpreted(args: Term ** N): K.Formula = underlyingLabel match {
      case label: K.PredicateLabel => K.PredicateFormula(label, args.toSeq.map(_.underlying))
      //case lambda : K.LambdaFormulaFormula => lambda(args.toSeq.map(_.underlying))
    }

    def app(args: Term ** N): AppliedPredicate[N] = AppliedPredicate[N](this, args.toSeq)
    def rename(newid: K.Identifier):PredicateLabel[N]
  }

  case class SchematicPredicateLabel[N <: Arity](id: K.Identifier, arity : N) extends PredicateLabel[N] with SchematicLabel[Term ** N |->Formula]{
    val underlyingLabel: K.SchematicPredicateLabel = K.SchematicPredicateLabel(id, arity)

    @nowarn
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): |->[Term ** N, Formula]  = {
      map.get(this.asInstanceOf) match {
        case Some(subst) => subst match {
          case s: |->[Term ** N, Formula]  => s
        }
        case None => this
      }
    }
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def rename(newid: K.Identifier):SchematicPredicateLabel[N] = SchematicPredicateLabel(newid, arity)

  }

  case class ConstantPredicateLabel[N <: Arity](id: K.Identifier, arity : N) extends PredicateLabel[N] with ConstantLabel[Term ** N |->Formula]{
    val underlyingLabel: K.ConstantPredicateLabel = K.ConstantPredicateLabel(id, arity)
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): this.type =
      this
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def rename(newid: K.Identifier):ConstantPredicateLabel[N] = ConstantPredicateLabel(newid, arity)
  }

  case class AppliedPredicate[N <: Arity](p: PredicateLabel[N], args: Seq[Term]) extends Formula with Absolute {
    override val underlying = p.interpreted(args)
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]):Formula =
      p.substituteUnsafe(map)(args.map[Term]((x:Term) => x.substituteUnsafe(map)))

    def freeSchematicLabels:Set[SchematicLabel[?]] = p.freeSchematicLabels ++ args.toSeq.flatMap(_.freeSchematicLabels)
    def allSchematicLabels:Set[SchematicLabel[?]] = p.allSchematicLabels ++ args.toSeq.flatMap(_.allSchematicLabels)
    //override def substituteUnsafe(v: Variable, subs: Term) = AppliedPredicateFormula[N](f, args.map(_.substituteUnsafe(v, subs)))
  }


  sealed trait ConnectorLabel[N <: Arity] extends |->[Formula ** N, Formula] with WithArity[N] with Absolute with Label[(Formula**N) |-> Formula] {
    val arity : N
    def id: K.Identifier
    val underlyingLabel: K.ConnectorLabel // | K.LambdaFormulaFormula
    def interpreted(args: Formula ** N): K.Formula = underlyingLabel match {
      case label : K.ConnectorLabel => K.ConnectorFormula(label, args.toSeq.map(_.underlying))
      //case lambda : K.LambdaFormulaFormula => lambda(args.toSeq.map(_.underlying))
    }
    def app(args: Formula ** N): AppliedConnector = AppliedConnector(this, args.toSeq)
    def rename(newid: K.Identifier):ConnectorLabel[N]

    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): |->[Formula ** N, Formula]

  }

  case class SchematicConnectorLabel[N <: Arity](id: K.Identifier, arity : N) extends ConnectorLabel[N] with SchematicLabel[Formula ** N |->Formula]{
    val underlyingLabel: K.SchematicConnectorLabel = K.SchematicConnectorLabel(id, arity)

    @nowarn
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): |->[Formula ** N, Formula] = {
      map.get(this.asInstanceOf) match {
        case Some(subst) => subst match {
          case s: |->[Formula ** N, Formula]  => s
        }
        case None => this
      }
    }
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def allSchematicLabels:Set[SchematicLabel[?]] = Set(this)
    def rename(newid: K.Identifier):SchematicConnectorLabel[N] = SchematicConnectorLabel(newid, arity)

  }

  trait ConstantConnectorLabel[N <: Arity] extends ConnectorLabel[N] with ConstantLabel[Formula ** N |->Formula]{
    val underlyingLabel: K.ConstantConnectorLabel
    def id: K.Identifier = underlyingLabel.id
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): this.type = this
    def freeSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def allSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    def rename(newid: K.Identifier):ConstantConnectorLabel[N] = throw new Error("Can't rename a constant connector label")

  }

  case class AppliedConnector(p: ConnectorLabel[?], args: Seq[Formula]) extends Formula with Absolute {
    assert(args.length == p.arity)
    override val underlying = p.interpreted(args)
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]):Formula = {
      val p2 = p.substituteUnsafe(map)
      p2 match {
        case p2 : ConnectorLabel[?] => AppliedConnector(p2, args.map[Formula]((x:Formula) => x.substituteUnsafe(map)))
        case _ => p2(args.map[Formula]((x:Formula) => x.substituteUnsafe(map)))
      }
    }

    def freeSchematicLabels:Set[SchematicLabel[?]] = p.freeSchematicLabels ++ args.flatMap(_.freeSchematicLabels)
    def allSchematicLabels:Set[SchematicLabel[?]] = p.allSchematicLabels ++ args.flatMap(_.allSchematicLabels)
    //override def substituteUnsafe(v: Variable, subs: Term) = AppliedPredicateFormula[N](f, args.map(_.substituteUnsafe(v, subs)))
  }


  abstract class BinderLabel extends |->[(Variable, Formula), Formula] with Absolute {
    def id: K.Identifier
  }

  trait BaseBinderLabel extends BinderLabel {
    val underlyingLabel: K.BinderLabel

    def app(arg: (Variable, Formula)): Formula = BaseQuantifiedFormula(this, arg._1, arg._2)
    inline def freeSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    inline def allSchematicLabels:Set[SchematicLabel[?]] = Set.empty
    inline def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): this.type = this

  }

  case class BaseQuantifiedFormula(f: BaseBinderLabel, bound: Variable, body: Formula) extends Formula with Absolute {
    override val underlying = K.BinderFormula(f.underlyingLabel, bound.underlyingLabel, body.underlying)

    def allSchematicLabels: Set[Common.this.SchematicLabel[?]] = body.allSchematicLabels+bound
    def freeSchematicLabels: Set[Common.this.SchematicLabel[?]] = body.freeSchematicLabels-bound
    def substituteUnsafe(map: Map[SchematicLabel[_], LisaObject[_]]): Formula = {
      val newSubst = map - bound.asInstanceOf
      if (map.values.flatMap(_.freeSchematicLabels).toSet.contains(bound)){
        val taken:Set[SchematicLabel[?]] = body.allSchematicLabels ++ map.keys
        val newBound:Variable = bound.rename(lisa.utils.KernelHelpers.freshId(taken.map(_.id), bound.id))
        val newBody = body.substituteOne(bound, newBound.lift)
        BaseQuantifiedFormula(f, newBound, newBody.substituteUnsafe(newSubst))
      } else {
        BaseQuantifiedFormula(f, bound, body.substituteUnsafe(newSubst))
      }
    }

  }
  def instantiateBinder(f: BaseQuantifiedFormula, t: Term): Formula = f.body.substituteUnsafe(Map(f.bound -> t))



}
