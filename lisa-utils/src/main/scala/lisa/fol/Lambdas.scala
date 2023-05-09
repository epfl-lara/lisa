package lisa.fol
import lisa.kernel.fol.FOL.Identifier
import FOLHelpers.freshId
import lisa.utils.K
trait Lambdas extends Common{

  case class LambdaExpression[T <: LisaObject[T],R <: LisaObject[R], N <: Arity](bounds:Seq[SchematicLabel[T]], body:R, arity:N) extends |->[T**N, R]{
    assert(arity == bounds.length)
    private val seqBounds = bounds.toSeq

    def app(args: T**N): R = body.substituteUnsafe((bounds zip args.toSeq).toMap)
    def appUnsafe(args: Seq[T]): R = body.substituteUnsafe((bounds zip args.toSeq).toMap)

    def substituteUnsafe(map: Map[SchematicLabel[_], _ <: LisaObject[_]]): LambdaExpression[T, R, N] = {
      val newSubst = map -- seqBounds
      val conflict = map.values.flatMap(_.freeSchematicLabels).toSet.intersect(bounds.asInstanceOf)
      if (conflict.nonEmpty) {
        val taken = (map.values.flatMap(_.allSchematicLabels).map(_.id) ++ map.keys.map(_.id)).toList
        val newBounds = seqBounds.scanLeft[List[Identifier]](taken)((list, v: SchematicLabel[T]) =>
          freshId(list, v.id) :: list
        ).map(_.head).zip(seqBounds).map(v => v._2.rename(v._1))
        val newBody = body.substituteUnsafe(seqBounds.zip(newBounds.map(_.lift)).toMap)
        LambdaExpression(newBounds, newBody.substituteUnsafe(newSubst), arity)
      } else{
        LambdaExpression(bounds, body.substituteUnsafe(newSubst), arity)
      }
    }

    def freeSchematicLabels:Set[SchematicLabel[?]] = body.freeSchematicLabels--seqBounds
    def allSchematicLabels:Set[SchematicLabel[?]] = body.freeSchematicLabels


    def underlying:Option[K.LambdaTermTerm|K.LambdaTermFormula|K.LambdaFormulaFormula] = this match {
      case l: LambdaExpression[Term, Term, N] => Some(underlyingLTT(l))
      case l: LambdaExpression[Term, Formula, N] => Some(underlyingLTF(l))
      case l: LambdaExpression[Formula, Formula, N] => Some(underlyingLFF(l))
      case _ => None
    }
  }

  def lambda[T <: LisaObject[T],R<:LisaObject[R]](bound:SchematicLabel[T], body:R) = LambdaExpression[T, R, 1](Seq(bound), body, 1)
  def lambda[T <: LisaObject[T], R<:LisaObject[R], N <: Arity](bounds:SchematicLabel[T]**N, body:R)(using n: ValueOf[N]) = {
    val boundsSeq = bounds.toSeq
    LambdaExpression[T, R, N](boundsSeq, body, n.value)
  }

  def underlyingLTT[N <: Arity](ltt: LambdaExpression[Term, Term, N]): K.LambdaTermTerm = 
    K.LambdaTermTerm(ltt.bounds.map(b => b.asInstanceOf[Variable].underlyingLabel), ltt.body.underlying)

  def underlyingLTF[N <: Arity](ltf: LambdaExpression[Term, Formula, N]): K.LambdaTermFormula = 
    K.LambdaTermFormula(ltf.bounds.map(b => b.asInstanceOf[Variable].underlyingLabel), ltf.body.underlying)

  def underlyingLFF[N <: Arity](lff: LambdaExpression[Formula, Formula, N]): K.LambdaFormulaFormula =  
    K.LambdaFormulaFormula(lff.bounds.map(b => b.asInstanceOf[VariableFormula].underlyingLabel), lff.body.underlying)


}
