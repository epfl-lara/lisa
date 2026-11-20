package lisa.maths.SetTheory.Types.ADT.interface

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADT.encoding.SemanticADT
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.generalTheorem
import lisa.maths.SetTheory.Types.ADT.support.core.Utils.renderAppliedSymbol
import lisa.maths.SetTheory.Types.ADT.support.core.Utils.typeExprToTerm
import lisa.maths.SetTheory.Types.ADT.syntax.AST._
import lisa.utils.prooflib.Thm

class ADT[S](using val line: sourcecode.Line, val file: sourcecode.File, sort: (S) is Sort)(
    val semantic: SemanticADT
) extends Constant[S](semantic.id) {

  printAs(args => renderAppliedSymbol(semantic.name, semantic.typeVariablesSeq.size, args))

  val name: String = semantic.name
  val typeVariablesSeq: Seq[Variable[Ind]] = semantic.typeVariablesSeq

  /**
   * Applies exactly the declared type arguments and returns a set.
   */
  def termAt(args: Seq[Expr[Ind]]): Expr[Ind] =
    require(args.size == typeVariablesSeq.size, s"ADT $name expects ${typeVariablesSeq.size} type argument(s), got ${args.size}.")
    (this #@@ args).asInstanceOf[Expr[Ind]]

  val term: Expr[Ind] = termAt(typeVariablesSeq)

  ADT.register(this)

  lazy val constructors: Seq[Constructor[S]] =
    semantic.constructors.iterator.map[Constructor[S]](c => new Constructor[S](c, this)).toVector

  /**
   * The structural induction principle, closed over this ADT's type variables.
   * Instantiate at type arguments with `of`, e.g. `list.induction of nat`.
   */
  lazy val induction: Theorem =
    generalTheorem(name, typeVariablesSeq, "induction", semantic.induction)

  /**
   * Every inhabitant is a constructor applied to typed arguments. Instantiate with `of`.
   */
  lazy val elim: Theorem =
    generalTheorem(name, typeVariablesSeq, "elimination", semantic.elim)

  private val disjointnessThms = scala.collection.mutable.Map.empty[(Constructor[S], Constructor[S]), Theorem]

  /**
   * Instances of two distinct constructors are never equal. Instantiate with `of`.
   */
  def disjointness(c1: Constructor[S], c2: Constructor[S]): Theorem =
    require(
      (c1.adt eq this) && (c2.adt eq this) && constructors.contains(c1) && constructors.contains(c2) && c1 != c2,
      s"$name has no disjointness between ${c1.name} and ${c2.name}; they must be two distinct constructors of $name."
    )
    disjointnessThms.getOrElseUpdate(
      (c1, c2),
      generalTheorem(
        name,
        typeVariablesSeq,
        s"${c1.semantic.name}-${c2.semantic.name}/disjointness",
        semantic.disjointness(c1.semantic, c2.semantic)
      )
    )

  def applySeq(args: Seq[Expr[Ind]]): Expr[Ind] = termAt(args)

  def apply(args: Expr[Ind]*): Expr[Ind] = termAt(args)

  def specialize(args: Expr[Ind]*): SpecializedADT[S] =
    new SpecializedADT[S](this, args)
}

object ADT {
  private val namesToADT: scala.collection.mutable.Map[String, ADT[?]] =
    scala.collection.mutable.Map.empty

  private val idsToADT: scala.collection.mutable.Map[Identifier, ADT[?]] =
    scala.collection.mutable.Map.empty

  private val constructorOwners: scala.collection.mutable.Map[Identifier, (ADT[?], Int)] =
    scala.collection.mutable.Map.empty

  private def register(adt: ADT[?]): Unit = {
    namesToADT.update(adt.name, adt)
    idsToADT.update(adt.id, adt)
    adt.semantic.constructors.zipWithIndex.foreach { (constructor, index) =>
      constructorOwners.update(constructor.id, (adt, index))
    }
  }

  def unapply(obj: Expr[Ind]): Option[(ADT[?], Seq[Expr[Ind]])] =
    obj match
      case c: Constant[?] @unchecked =>
        getADT(c.id).map((_, Seq.empty))
      case Multiapp(head, args) =>
        head match
          case c: Constant[?] @unchecked => getADT(c.id).map((_, args.asInstanceOf[Seq[Expr[Ind]]]))
          case _ => None

  def getADT(name: String): Option[ADT[?]] = namesToADT.get(name)

  def getADT(id: Identifier): Option[ADT[?]] = idsToADT.get(id)

  /**
   * Looks up a constructor by identifier, initializing only its owner's constructor wrappers.
   */
  // Here private[ADT] would refer to this object rather than the enclosing package.
  private[Types] def getConstructor(id: Identifier): Option[Constructor[?]] =
    constructorOwners.get(id).map((adt, index) => adt.constructors(index))

  def allADTs: Iterable[ADT[?]] = namesToADT.values
}
