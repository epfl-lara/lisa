package lisa.front.fol.ops

import lisa.front.fol.definitions.TermDefinitions

trait TermOps extends TermDefinitions with CommonOps {

  extension[N <: Arity] (label: TermLabel[N]) {
    def apply(args: FillArgs[Term, N]): Term = Term.unsafe(label, tuple2seq(args))
  }
  //extension (label: TermLabel[2])
  //  def apply(a: Term, b: Term): Term = Term.unsafe(label, Seq(a, b))
  //extension (label: TermLabel[1])
  //  def apply(a: Term): Term = Term.unsafe(label, Seq(a))
  extension (label: TermLabel[0]) { def apply(): Term = Term.unsafe(label, Seq.empty) }

  given Conversion[ConstantFunctionLabel[0], Term] = Term.unsafe(_, Seq.empty)
  given Conversion[SchematicTermLabel[0], Term] = Term.unsafe(_, Seq.empty)
  given Conversion[TermLabel[0], Term] = Term.unsafe(_, Seq.empty)

  @deprecated
  given Conversion[Term, TermLabel[?]] = _.label

}
