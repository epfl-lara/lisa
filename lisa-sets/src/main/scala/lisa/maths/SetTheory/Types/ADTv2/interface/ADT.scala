package lisa.maths.SetTheory.Types.ADTv2.interface

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.maths.SetTheory.Types.ADTv2.encoding.SemanticADT
import lisa.maths.SetTheory.Types.ADTv2.support.{**, toSeq}
import lisa.maths.SetTheory.Types.ADTv2.support.InterfaceHelpers.theoremAt
import lisa.maths.SetTheory.Types.ADTv2.support.Printing
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.{renderAppliedSymbol, typeExprToTerm}
import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.utils.prooflib.ProofTacticLib.Arity

final class ADT[N <: Arity](using val line: sourcecode.Line, val file: sourcecode.File, valueOfN: ValueOf[N])(
    val semantic: SemanticADT[N]
) extends Constant[Ind](semantic.id) {

  Printing.install()
  printAs(args => renderAppliedSymbol(semantic.name, semantic.typeVariablesSeq.size, args))

  val name: String = semantic.name
  val typeVariables: Variable[Ind] ** N = semantic.typeVariables
  val typeVariablesSeq: Seq[Variable[Ind]] = semantic.typeVariablesSeq
  val get_arity: Int = valueOfN.value

  val term: Expr[Ind] = termAt(typeVariablesSeq)

  ADT.register(this)

  lazy val constructors: Seq[Constructor[N]] =
    semantic.constructors.map(c => new Constructor[N](c))

  lazy val induction: THM = theoremAt(
    displayName = name,
    typeVariables = typeVariablesSeq,
    typeArgs = Seq.empty,
    suffix = "induction",
    baseTheorem = semantic.induction
  )

  lazy val elim: THM = theoremAt(
    displayName = name,
    typeVariables = typeVariablesSeq,
    typeArgs = Seq.empty,
    suffix = "elimination",
    baseTheorem = semantic.elim
  )

  def injectivity(c1: Constructor[N], c2: Constructor[N]): THM =
    theoremAt(
      displayName = name,
      typeVariables = typeVariablesSeq,
      typeArgs = Seq.empty,
      suffix = s"${c1.semantic.name}-${c2.semantic.name}/injectivity",
      baseTheorem = semantic.injectivity(c1.semantic, c2.semantic)
    )

  def inductionAt(typeArgs: Expr[Ind]*): THM =
    theoremAt(name, typeVariablesSeq, typeArgs, "induction", semantic.induction)

  def elimAt(typeArgs: Expr[Ind]*): THM =
    theoremAt(name, typeVariablesSeq, typeArgs, "elimination", semantic.elim)

  def injectivityAt(
      c1: Constructor[N],
      c2: Constructor[N],
      typeArgs: Expr[Ind]*
  ): THM =
    theoremAt(
      name,
      typeVariablesSeq,
      typeArgs,
      s"${c1.semantic.name}-${c2.semantic.name}/injectivity",
      semantic.injectivity(c1.semantic, c2.semantic)
    )

  def termAt(args: Seq[Expr[Ind]]): Expr[Ind] = semantic.term(args)

  def applyUnsafe(args: Expr[Ind] ** N): Expr[Ind] = termAt(args.toSeq)

  def applySeq(args: Seq[Expr[Ind]]): Expr[Ind] = termAt(args)

  def apply(args: Expr[Ind]*): Expr[Ind] = termAt(args)

  def applyType(args: TypeExpr*): Expr[Ind] =
    applySeq(args.map(typeExprToTerm))
}

object ADT {
  private val namesToADT: scala.collection.mutable.Map[String, ADT[?]] =
    scala.collection.mutable.Map.empty

  private val idsToADT: scala.collection.mutable.Map[Identifier, ADT[?]] =
    scala.collection.mutable.Map.empty

  private def register(adt: ADT[?]): Unit = {
    namesToADT.update(adt.name, adt)
    idsToADT.update(adt.id, adt)
  }

  def unapply(t: TypeRef): Option[ADT[?]] = getADT(t.name)

  def unapply(obj: TypeExpr): Option[(ADT[?], Seq[TypeExpr])] = obj match
    case TypeRef(name) => getADT(name).map((_, Seq.empty))
    case TypeApply(name, args) => getADT(name).map((_, args))

  def unapply(obj: Expr[Ind]): Option[(ADT[?], Seq[Expr[Ind]])] =
    obj match
      case c: Constant[Ind] @unchecked =>
        getADT(c.id).map((_, Seq.empty))
      case Multiapp(head, args) =>
        head match
          case c: Constant[Ind] @unchecked => getADT(c.id).map((_, args.asInstanceOf[Seq[Expr[Ind]]]))
          case _ => None

  def getADT(name: String): Option[ADT[?]] = namesToADT.get(name)

  def getADT(id: Identifier): Option[ADT[?]] = idsToADT.get(id)

  def allADTs: Iterable[ADT[?]] = namesToADT.values
}
