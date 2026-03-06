package lisa.maths.SetTheory.Types.ADTv2.interpreters

/** Type-theoretic bridge for ADT v2. */
object TypeTheoreticInterpreter {

  final case class TypedADT(raw: Any)

  def fromSetTheoretic(result: SetTheoreticInterpreter.Result): TypedADT =
    TypedADT(result.adt)
}
