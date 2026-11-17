package lisa.maths.SetTheory.Types.ADTv2.PatternMatching

import lisa.maths.SetTheory.SetTheory.{_, given}
import lisa.maths.SetTheory.Types.ADTv2.interface.ADT
import lisa.maths.SetTheory.Types.ADTv2.interface.Constructor
import lisa.maths.SetTheory.Types.ADTv2.interface.SpecializedADT
import lisa.maths.SetTheory.Types.TypingHelpers

/**
 * Resolves constructor patterns without generating proofs or registering definitions.
 */
private[PatternMatching] object PatternValidation {

  /**
   * Separates a set application into its head and ordered value arguments.
   */
  def peelApp(term: Expr[Ind]): (Expr[Ind], List[Expr[Ind]]) = {
    @annotation.tailrec
    def loop(current: Expr[Ind], args: List[Expr[Ind]]): (Expr[Ind], List[Expr[Ind]]) =
      TypingHelpers.`*`.unapply(current) match
        case Some((head, arg)) => loop(head, arg :: args)
        case None => (current, args)
    loop(term, Nil)
  }

  /**
   * Decodes a fully applied registered constructor, preserving its explicit type arguments.
   */
  def constructorApplication(term: Expr[Ind]): Either[String, (Constructor[?], Seq[Expr[Ind]], List[Expr[Ind]])] = {
    val (head, args) = peelApp(term)
    head match
      case Multiapp(symbol: Constant[?] @unchecked, typeArgs) =>
        ADT.getConstructor(symbol.id) match
          case None => Left(s"Unsupported pattern $term: expected a variable or a constructor application.")
          case Some(constructor) =>
            if typeArgs.size != constructor.typeVariablesSeq.size then Left(s"Constructor ${constructor.name} expects ${constructor.typeVariablesSeq.size} type argument(s), got ${typeArgs.size}.")
            else if !typeArgs.forall(_.sort == summon[Sort[Ind]].underlying) then Left(s"Constructor ${constructor.name} requires type arguments of sort Ind.")
            else if args.size != constructor.semantic.arity then Left(s"Constructor ${constructor.name} expects ${constructor.semantic.arity} value argument(s), got ${args.size}.")
            else Right((constructor, typeArgs.asInstanceOf[Seq[Expr[Ind]]], args))
      case _ => Left(s"Unsupported pattern $term: expected a variable or a constructor application.")
  }

  /**
   * Resolves one case while checking ownership, specialization, arities, and binder linearity.
   */
  def resolveCase(constructor: Constructor[?], args: Seq[Expr[Ind]], domain: SpecializedADT[?]): Either[String, PatternNode.Construct] =
    new Resolver().constructor(constructor, domain.typeArgs, args, domain.term, s"Case ${constructor.name}")

  private final class Resolver {
    private val binders = scala.collection.mutable.HashSet.empty[Variable[Ind]]

    def node(term: Expr[Ind], expectedType: Expr[Ind], path: String): Either[String, PatternNode] = term match
      case v: Variable[Ind] @unchecked =>
        Either.cond(binders.add(v), PatternNode.Bind(v, expectedType), s"$path: repeated pattern binder $v.")
      case _ =>
        constructorApplication(term).left.map(error => s"$path: $error").flatMap { (cons, typeArgs, values) =>
          constructor(cons, typeArgs, values, expectedType, path)
        }

    def constructor(
        cons: Constructor[?],
        typeArgs: Seq[Expr[Ind]],
        values: Seq[Expr[Ind]],
        expectedType: Expr[Ind],
        path: String
    ): Either[String, PatternNode.Construct] =
      ADT.unapply(expectedType) match
        case None => Left(s"$path: cannot match constructor ${cons.name} at non-ADT type $expectedType.")
        case Some((adt, _)) if adt.id != cons.adt.id =>
          Left(s"$path: ${cons.name} is not a constructor of $expectedType.")
        case _ if !isSame(cons.adt.termAt(typeArgs), expectedType) =>
          Left(s"$path: constructor type arguments give ${cons.adt.termAt(typeArgs)}, expected $expectedType.")
        case _ if values.size != cons.semantic.arity =>
          Left(s"$path: expected ${cons.semantic.arity} value argument(s), got ${values.size}.")
        case _ =>
          val substitutions = cons.typeVariablesSeq.zip(typeArgs).map((v, arg) => v := arg)
          val arguments = List.newBuilder[PatternNode]
          val children = values.iterator.zip(cons.semantic.semanticSignature).zipWithIndex
          while children.hasNext do
            val ((value, (_, typ)), index) = children.next()
            node(value, typ.substitute(substitutions*), s"$path argument ${index + 1}") match
              case Left(error) => return Left(error)
              case Right(argument) => arguments += argument
          Right(PatternNode.Construct(cons, typeArgs, arguments.result()))
  }
}
