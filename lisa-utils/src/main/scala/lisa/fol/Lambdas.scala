package lisa.fol
import lisa.kernel.fol.FOL.Identifier
import FOLHelpers.freshId
trait Lambdas extends Common{

  case class LambdaExpression[T <: LisaObject[T],R <: LisaObject[R], N <: Arity](bounds:Seq[SchematicLabel[T]], body:R, arity:N) extends |->[T**N, R]{
    assert(arity == bounds.length)
    private val seqBounds = bounds.toSeq

    def app(args: T**N): R = body.substitute((bounds zip args.toSeq).toMap)
/*
    def substitute[S <: LisaObject[S]](v: SchematicLabel[S], arg: S): |->[T, R] = {
      if (bound == v) this
      else if/*arg.freeSymbols.contains bound*/ (false) {
        val taken:Set[SchematicLabel[?]] = body.allSchematicLabels
        val newBound:SchematicLabel[T] = bound.rename(lisa.utils.KernelHelpers.freshId(taken.map(_.id), bound.id))
        val newBody = body.substitute(bound, newBound.lift)
        LambdaExpression(newBound, newBody.substitute(v, arg))
      } else {
        LambdaExpression(bound, body.substitute(v, arg))
      }
    }
 */
    def substitute[S <: LisaObject[S]](map: Map[SchematicLabel[S], S]): LambdaExpression[T, R, N] = {
      val newSubst = map -- seqBounds.asInstanceOf
      val conflict = map.values.flatMap(_.freeSchematicLabels).toSet.intersect(bounds.asInstanceOf)
      if (conflict.nonEmpty) {
        val taken = (map.values.flatMap(_.allSchematicLabels).map(_.id) ++ map.keys.map(_.id)).toList
        val newBounds = seqBounds.scanLeft[List[Identifier]](taken)((list, v: SchematicLabel[T]) =>
          freshId(list, v.id) :: list
        ).map(_.head).zip(seqBounds).map(v => v._2.rename(v._1))
        val newBody = body.substitute(seqBounds.zip(newBounds.map(_.lift)).toMap)
        LambdaExpression(newBounds, newBody.substitute(newSubst), arity)
      } else{
        LambdaExpression(bounds, body.substitute(newSubst), arity)
      }
    }

    def freeSchematicLabels:Set[SchematicLabel[?]] = body.freeSchematicLabels--seqBounds
    def allSchematicLabels:Set[SchematicLabel[?]] = body.freeSchematicLabels
  }

  def lambda[T <: LisaObject[T],R<:LisaObject[R]](bound:SchematicLabel[T], body:R) = LambdaExpression[T, R, 1](Seq(bound), body, 1)
  def lambda[T <: LisaObject[T], R<:LisaObject[R], N <: Arity](bounds:SchematicLabel[T]**N, body:R)(using n: ValueOf[N]) = {
    val boundsSeq = bounds.toSeq
    LambdaExpression[T, R, N](boundsSeq, body, n.value)
  }





}
