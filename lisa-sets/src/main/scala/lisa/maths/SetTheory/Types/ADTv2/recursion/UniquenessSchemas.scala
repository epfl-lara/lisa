package lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.Types.ADTv2.encoding.*
import lisa.maths.SetTheory.Types.ADTv2.support.core.Utils.*
import lisa.maths.SetTheory.Types.TypingHelpers.*
import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.fol.FOL.App
import lisa.utils.prooflib.ProofTacticLib.Arity

type ConstructorSchemas[N <: Arity] =
  Map[SemanticConstructor[N], (Seq[Variable[Ind]], Expr[Prop])]

def asIndEquality(formula: Expr[Prop]): Option[(Expr[Ind], Expr[Ind])] = formula match
  case App(App(eqFun, lhs: Expr[Ind]), rhs: Expr[Ind]) if eqFun == equality => Some((lhs, rhs))
  case _ => None

def splitConjunctions(formula: Expr[Prop]): Seq[Expr[Prop]] = formula match
  case left /\ right => splitConjunctions(left) ++ splitConjunctions(right)
  case other => Seq(other)

def stripForalls(formula: Expr[Prop]): (Seq[Variable[Ind]], Expr[Prop]) = formula match
  case forall(v, phi) =>
    val (restVars, core) = stripForalls(phi)
    (v +: restVars, core)
  case other => (Seq.empty, other)

def extractConstructorCaseSchema[N <: Arity](
    definition: Expr[Prop],
    functionHead: Expr[Ind],
    constructor: SemanticConstructor[N]
): (Seq[Variable[Ind]], Expr[Prop]) = {
  val maybeSchema = splitConjunctions(definition).iterator.flatMap(candidate =>
    val (vars, core) = stripForalls(candidate)
    val maybeEquality = core match
      case _ ==> equalityFormula => asIndEquality(equalityFormula)
      case equalityFormula       => asIndEquality(equalityFormula)

    maybeEquality.flatMap((lhs, _) =>
      lhs match
        case Sapp(fun: Expr[Ind], arg: Expr[Ind])
            if fun == functionHead && arg == constructor.appliedTerm(vars) =>
          Some(vars -> candidate)
        case _ => None
    )
  ).toSeq.headOption

  maybeSchema.getOrElse(
    throw IllegalArgumentException(
      s"Unable to extract constructor case schema for constructor ${constructor.name} and function ${functionHead}."
    )
  )
}
