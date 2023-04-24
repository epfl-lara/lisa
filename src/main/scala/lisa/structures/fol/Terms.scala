package lisa.structures.fol

import lisa.kernel.fol.FOL
import lisa.settheory.SetTheoryLibrary


import scala.annotation.showAsInfix
import scala.compiletime.ops.int.-


trait Terms extends Common {

  @showAsInfix
  abstract class |->[-I, +O <: LisaObject] extends (I => O) {
    def app(arg: I): O
    def apply(arg:I) : O = app(arg)

  }


  abstract class Term extends LisaObject {
    val underlying: FOL.Term

    def substituteUnsafe(v: Variable, t: Term): Term

    final def substitute(v: Variable, t: Term): Term = {
      val r = substituteUnsafe(v, t)
      assert(r.underlying == FOL.substituteVariables(underlying, Map((FOL.VariableLabel(v.id), t.underlying))))
      r
    }

  }

  /////////////////////
  // Matching Kernel //
  /////////////////////


  trait Absolute

  case class Variable(id: FOL.Identifier) extends Term with Absolute with SchematicLabel {
    val underlyingLabel: FOL.VariableLabel = FOL.VariableLabel(id)
    val underlying = FOL.VariableTerm(underlyingLabel)

    override def substituteUnsafe(v: Variable, t: Term): Term = if (v.id == id) t else this
  }

  case class Constant(id: FOL.Identifier) extends Term with Absolute with ConstantLabel {
    val underlyingLabel: FOL.ConstantFunctionLabel = FOL.ConstantFunctionLabel(id, 0)
    val underlying = FOL.Term(underlyingLabel, Seq())

    override def substituteUnsafe(v: Variable, t: Term): Term = this
  }

  sealed trait FunctionalLabel[N <: Arity : ValueOf] extends |->[Term ** N, Term] with WithArity[N] with Absolute{
    val arity = valueOf[N]
    val id:FOL.Identifier
    val underlyingLabel: FOL.TermLabel
    def app(args: Term ** N): AppliedTerm[N] = AppliedTerm[N](this, args.toSeq)
  }

  case class ConstantFunctionalLabel[N <: Arity : ValueOf](id: FOL.Identifier) extends FunctionalLabel[N] with ConstantLabel  {
    val underlyingLabel: FOL.ConstantFunctionLabel = FOL.ConstantFunctionLabel(id, arity)

  }
  case class SchematicFunctionalLabel[N <: Arity : ValueOf](id: FOL.Identifier) extends FunctionalLabel[N] with SchematicLabel  {
    val underlyingLabel: FOL.SchematicFunctionLabel = FOL.SchematicFunctionLabel(id, arity)

  }

  case class AppliedTerm[N <: Arity : ValueOf](f: FunctionalLabel[N], args: Seq[Term]) extends Term with Absolute {
    require(isLegalApplication(f, args), "The number of arguments does not match the arity")
    override val underlying = FOL.Term(f.underlyingLabel, args.map(_.underlying))

    override def substituteUnsafe(v: Variable, subs: Term) = AppliedTerm[N](f, args.map(_.substituteUnsafe(v, subs)))
  }


  /*
  abstract class LocalTerm(val proof: SetTheoryLibrary.Proof) extends Term {
    val properties = ???
  }

   */

}
