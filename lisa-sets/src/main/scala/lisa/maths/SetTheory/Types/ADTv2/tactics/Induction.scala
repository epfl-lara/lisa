package lisa.maths.SetTheory.Types.ADTv2.tactics

import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.*
import lisa.maths.SetTheory.Types.ADTv2.interface.{ADT, Constructor}
import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.*
import lisa.maths.SetTheory.Types.ADTv2.support.Utils.*
import lisa.maths.SetTheory.Types.ADTv2.functions.CaseAccumulator

import lisa.utils.prooflib.ProofTacticLib.Arity
import lisa.maths.SetTheory.Types.TypingHelpers.{::, TypeAssign}
import lisa.maths.SetTheory.SetTheory.{*, given}

/**
 *  Tactic performing a structural induction proof over an algebraic data type.
 *
 *  ===Usage===
 *  {{{
 *  have(forall(x, x :: adt => P(x)) /*or*/ x :: adt |- P(x)) by Induction(x, adt) {
 *    Case(c1, x1, ..., xn) subproof {
 *      // proof of P(xi) /\ ... P(xj) => P(c1(x1, ..., xn))
 *    }
 *    ...
 *    Case(cm, x1, ..., xk) subproof {
 *      // proof of P(xi) /\ ... P(xj) => P(c1(x1, ..., xn'))
 *    }
 *  }
 *  }}}
 *
 *  x and adt are inferred from the context if not provided by the user.
 *
 *  Supports only 1 formula on the right hand side of the sequent.
 *  @param expectedVar the variable on which the induction is performed
 *  @param expectedADT the algebraic data type on which the induction is performed
 */
class Induction[M <: Arity](
    expectedVar: Option[Variable[Ind]],
    expectedADT: Option[ADT[M]]
) extends lisa.utils.prooflib.ProofTacticLib.ProofTactic {

  /**
   *  Given a proof of the claim for each case (possibly using the induction hypothesis),
   *  reassemble them to generate a proof of the claim of the form `∀x. x :: adt => P(x)`
   *
   *  @param proof the proof in which the induction is performed
   *  @param cases the proofs of the claim for each case in addition to the variables used
   *    by the user
   *  @param inductionVariable the variable over which the induction is performed
   *  @param adt the algebraic data type to perform induction on
   *  @param prop the property to prove //TODO: Change to a lambda expression (Scala
   *    3.4.2)
   */
  private def proveForallPredicate[N <: Arity](using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      cases: Map[Constructor[N], (Seq[Variable[Ind]], proof.Fact)],
      inductionVariable: Variable[Ind],
      adt: ADT[N],
      typeVariablesSubst: Seq[Expr[Ind]],
      propFun: Expr[Ind] => Expr[Prop],
      context: Set[Expr[Prop]]
  ): proof.Fact =

    val prop = λ(x, propFun(x))
    val typeVariablesSubstPairs = adt.typeVariables.toSeq.zip(typeVariablesSubst)
      .map(SubstPair(_, _))
    val instTerm = adt.semantic.term(typeVariablesSubst)

    val instantiatedInduction = have(
      adt.semantic.induction.statement.substitute((typeVariablesSubstPairs :+ (P := prop))*)
    ) by Restate.from(adt.semantic.induction.of((typeVariablesSubstPairs :+ (P := prop))*))

    adt.constructors.foldLeft[proof.Fact](instantiatedInduction)((acc, c) =>
      val inductiveCaseProof = cases(c)._1.zip(
        c.semantic.underlying.specification
      ).foldRight[proof.Fact](cases(c)._2)((el, acc2) =>
        val (v, ty) = el
        val accRight: Expr[Prop] = acc2.statement.right.head
        ty match
          case SelfRef =>
            have((acc2.statement -<? prop(v)).left |- prop(v) ==> accRight) by
              Weakening(acc2)
            thenHave(
              (lastStep.statement -<? (v :: instTerm)).left |-
                v :: instTerm ==> (prop(v) ==> accRight)
            ) by Weakening
            thenHave(
              lastStep.statement.left |-
                forall(v, v :: instTerm ==> (prop(v) ==> accRight))
            ) by RightForall
          // case RegularArg(t_) =>
          case TypeArg(typeName) =>
            val t = typeExprToTerm(typeName)
            thenHave((acc2.statement -<? (v :: t)).left |- v :: t ==> accRight) by
              Weakening
            thenHave(lastStep.statement.left |- forall(v, v :: t ==> accRight)) by
              RightForall
      )
      acc.statement.right.head match
        case implies(_, rest) =>
          have((acc.statement.left ++ inductiveCaseProof.statement.left) |- rest) by
            Tautology.from(acc, inductiveCaseProof)
        case _ => throw UnreachableException
    )
    thenHave(
      context |- forall(
        inductionVariable,
        inductionVariable :: instTerm ==> prop(inductionVariable)
      )
    ) by Tautology // Change

  private def checkFoundArguments(
      foundVar: Variable[Ind],
      foundADT: ADT[?],
      args: Seq[Expr[Ind]]
  ): Option[(Variable[Ind], ADT[?], Seq[Expr[Ind]])] = (expectedVar, expectedADT) match
    case (Some(v), _) if v != foundVar => None
    case (_, Some(a)) if a != foundADT => None
    case _ => Some((foundVar, foundADT, args))

  private def parseTypeExprRepr(repr: String): Option[TypeExpr] =
    def splitTopLevelArgs(raw: String): Option[Seq[String]] =
      if raw.isEmpty then Some(Seq.empty)
      else
        val args = scala.collection.mutable.ArrayBuffer.empty[String]
        val current = new StringBuilder
        var depth = 0
        var i = 0
        var bad = false
        val n = raw.length
        while i < n && !bad do
          raw.charAt(i) match
            case '[' =>
              depth += 1
              current.append('[')
            case ']' =>
              depth -= 1
              if depth < 0 then bad = true
              else current.append(']')
            case ',' if depth == 0 =>
              val arg = current.toString.trim
              if arg.isEmpty then bad = true
              else
                args += arg
                current.clear()
            case ch => current.append(ch)
          i += 1

        if bad || depth != 0 then None
        else
          val lastArg = current.toString.trim
          if lastArg.isEmpty then None
          else
            args += lastArg
            Some(args.toSeq)

    val s = repr.trim
    if s.isEmpty then None
    else
      val bracketIdx = s.indexOf('[')
      if bracketIdx < 0 then Some(TypeRef(s))
      else if !s.endsWith("]") then None
      else
        val name = s.substring(0, bracketIdx)
        val inner = s.substring(bracketIdx + 1, s.length - 1)
        splitTopLevelArgs(inner).flatMap { args =>
          args.foldLeft[Option[Seq[TypeExpr]]](Some(Seq.empty)) { (acc, arg) =>
            acc.flatMap(seq => parseTypeExprRepr(arg).map(seq :+ _))
          }.map(parsed => TypeApply(name, parsed))
        }

  private def typeTermToTypeExpr(term: Expr[Ind]): Option[TypeExpr] = {

    
    def parseTypeExprArgs(args: Seq[Expr[?]]): Option[Seq[TypeExpr]] = 
      args.foldLeft[Option[Seq[TypeExpr]]](Some(Seq.empty))((acc, arg) =>
        acc.flatMap(parsed =>
          typeTermToTypeExpr(arg.asInstanceOf[Expr[Ind]]).map(parsed :+ _)
        )
      )

    val (head, args) = unfoldAllApp(term)
    val maybeADT = ADT.allADTs.collectFirst {
      case adt if adt.semantic.underlying.polymorphicTerm == head => adt
    }

    maybeADT
      .flatMap(adt =>
        parseTypeExprArgs(args).map(typeArgs =>
          if typeArgs.isEmpty then TypeRef(adt.name) else TypeApply(adt.name, typeArgs)
        )
      )
      .orElse(
        head match
          case c: Constant[Ind] @unchecked =>
            parseTypeExprArgs(args).flatMap(parsedArgs =>
              parseTypeExprRepr(c.id.name).map {
                case TypeRef(name) if parsedArgs.nonEmpty => TypeApply(name, parsedArgs)
                case base if parsedArgs.isEmpty => base
                case _ => TypeApply(c.id.name, parsedArgs)
              }
            )
          case _ => None
      )
  }

  private def inferADTFromTypeTerm(
      typeTerm: Expr[Ind]
  ): Option[(ADT[?], Seq[Expr[Ind]])] = typeTermToTypeExpr(typeTerm)
    .flatMap((tpe: TypeExpr) => ADT.unapply(tpe)).map { case (adt, typeArgs) =>
      (adt, typeArgs.map(typeExprToTerm))
    }

  /**
   *  Infers the variable, the ADT and the arguments of the ADT from a formula of the form
   *  `x :: ADT(T1, ..., Tn)`.
   *
   *  @param f the formula to infer these elements from
   */
  def inferArguments(f: Expr[Prop]): Option[(Variable[Ind], ADT[?], Seq[Expr[Ind]])] =

    f match
      case TypeAssign(Variable[Ind](id), typeTerm) => inferADTFromTypeTerm(typeTerm)
          .flatMap { case (foundADT, args) =>
            checkFoundArguments(Variable[Ind](id), foundADT, args)
          }
      case _ => None

  /**
   *  Infers the variable, the ADT and the arguments of the ADT from a set of formula
   *  containing one is of the form `x :: ADT(T1, ..., Tn)`.
   *
   *  @param s the set of formula to infer these elements from
   */
  def inferArguments(
      s: Set[Expr[Prop]]
  ): Option[(Variable[Ind], ADT[?], Seq[Expr[Ind]])] = s
    .foldLeft[Option[(Variable[Ind], ADT[?], Seq[Expr[Ind]])]](None)((acc, prem) =>
      acc.orElse(inferArguments(prem))
    )

  /**
   *  Infers the variable, the ADT and the arguments of the ADT from a sequent whose one
   *  of the premises is of the form `x :: ADT(T1, ..., Tn)`.
   *
   *  @param seq the sequent to infer these elements from
   */
  def inferArguments(
      seq: Sequent
  ): Option[(Variable[Ind], ADT[?], Seq[Expr[Ind]], Option[Expr[Prop]])] = inferArguments(
    seq.left
  ).map(p => (p._1, p._2, p._3, None)).orElse(
    seq.right.head match
      case forall(x, implies(assignment, prop)) => inferArguments(assignment)
          .filter(p => p._1 == x).map(p => (p._1, p._2, p._3, Some(prop)))
      case _ => None
  )

  /**
   *  Fallback when ADT typing is not explicitly present in the sequent context.
   *
   *  This enables calls such as `Induction(x, nat)` on goals of the form `|- P(x)`.
   */
  private def inferArgumentsFromExpected(
      seq: Sequent
  ): Option[(Variable[Ind], ADT[?], Seq[Expr[Ind]], Option[Expr[Prop]])] =
    (expectedVar, expectedADT) match
      case (Some(v), Some(a)) =>
        // By default instantiate ADT type parameters with their schematic variables.
        Some((v, a, a.typeVariables.toSeq, None))
      case _ => None

  /**
   *  Given a proof of the claim for each case (possibly using the induction hypothesis),
   *  reassemble the subproofs to generate a proof of the claim for every element of the
   *  ADT.
   *
   *  @tparam N the arity of the ADT
   *  @param proof the scope in which the induction is performed
   *  @param cases the cases to prove. A [[CaseAccumulator]] is a mutable data structure
   *    that register every case that has been added to the tactic.
   *  @param bot the claim
   */
  def apply[N <: Arity](using
      proof: lisa.SetTheoryLibrary.Proof
  )(
      cases: CaseAccumulator[
        N,
        proof.ProofStep,
        (Sequent, Seq[Expr[Ind]], Variable[Ind])
      ] ?=> Unit
  )(bot: Sequent): proof.ProofTacticJudgement = inferArguments(bot)
    .orElse(inferArgumentsFromExpected(bot)) match
    case Some((inferedVar, inferedADT, inferedArgs, inferedProp)) =>

      val prop = inferedProp.getOrElse(bot.right.head)
      val propFunction = (t: Expr[Ind]) =>
        inferedProp.getOrElse(bot.right.head).substitute(inferedVar -> t)
      val assignment = inferedVar :: inferedADT.semantic.term(inferedArgs)

      val missingTypingAssumption =
        inferedProp.isEmpty &&
          !bot.left.contains(assignment) &&
          bot.freeVars.contains(inferedVar)

      if missingTypingAssumption then
        proof.InvalidProofTactic(
          s"Induction on variable '$inferedVar' over ADT '${inferedADT.name}' requires the typing assumption '$assignment' in the goal context. " +
            s"Current goal is '$bot'. Add '( $assignment ) |- ...', or restate the goal as a universally quantified statement " +
            s"'|- forall($inferedVar, $assignment ==> P($inferedVar))'."
        )
      else
        val context = (if inferedProp.isDefined then bot else bot -<< assignment).left
        val builder =
          CaseAccumulator[N, proof.ProofStep, (Sequent, Seq[Expr[Ind]], Variable[Ind])] (
            (context |- prop, inferedArgs, inferedVar)
          )
        cases(using builder)

        builder.isValid(inferedADT.asInstanceOf[ADT[N]]) match
          case None => TacticSubproof { sp ?=>
              proveForallPredicate(using sp)(
                builder.build,
                inferedVar,
                inferedADT.asInstanceOf[ADT[N]],
                inferedArgs,
                propFunction,
                context
              )
              if !inferedProp.isDefined then
                lastStep.statement.right.head match
                  case forall(_, phi) => thenHave(context |- phi) by
                      InstantiateForall(inferedVar)
                  case _ => throw UnreachableException

              thenHave(bot) by Tautology
            }
          case Some(msg) => proof.InvalidProofTactic(msg)

    case None => proof
        .InvalidProofTactic("No variable typed with the ADT found in the context.")

}

/** Placeholder for ADT v2 induction tactic implementation. */
object Induction {
  def apply()(using proof: lisa.SetTheoryLibrary.Proof) = new Induction(None, None)

  def apply[N <: Arity](adt: ADT[N])(using proof: lisa.SetTheoryLibrary.Proof) =
    new Induction(None, Some(adt))

  def apply(v: Variable[Ind])(using proof: lisa.SetTheoryLibrary.Proof) =
    new Induction(Some(v), None)

  def apply[N <: Arity](v: Variable[Ind], adt: ADT[N])(using
      proof: lisa.SetTheoryLibrary.Proof
  ) = new Induction(Some(v), Some(adt))
}
