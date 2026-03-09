package lisa.hol
import lisa.SetTheoryLibrary
import lisa.automation._
import lisa.hol.VarsAndFunctions._
import lisa.maths.SetTheory.Base.Predef.∈
import lisa.maths.SetTheory.Functions.Predef.{_, given}
import lisa.maths.SetTheory.Types
import lisa.maths.SetTheory.Types.Tactics.Typecheck
import lisa.utils.K
import lisa.utils.UserLisaException
import lisa.utils.fol.FOL._
import lisa.utils.prooflib.BasicStepTactic._
import lisa.utils.prooflib.ProofTacticLib.ProofTactic
import scala.collection.mutable

import SetTheoryLibrary.{have, JUSTIFICATION, thesis, THM, Proof, Theorem}
import lisa.utils.prooflib.BasicStepTactic.Weakening

import lisa.hol.Import.mkTypedVar


object ExtendedHOLSteps {

  import lisa.hol.HOLHelperTheorems.{One, nonEmptyFuncSpace, assume, eqRefl}
  import K.repr
  


  object _INST_TYPE_RENAME extends ProofTactic {
    def allTypedVars(e: Expr[?]): Set[(TypedVariable, Expr[Ind])] = e match
      case v: TypedVariable => Set((v, v.typ))
      case App(func, arg) => allTypedVars(func) ++ allTypedVars(arg)
      case Abs(v: TypedVariable, body) =>
        allTypedVars(body) + ((v, v.typ): (TypedVariable, Expr[Ind]))
      case Abs(v, body) => allTypedVars(v) ++ allTypedVars(body)
      case _ => Set.empty

    def variableTypesNames(using proof: Proof)(prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      val variablesSubst : mutable.Map[Variable[Ind], Variable[Ind]] = mutable.Map.empty
      val allvars = prem.statement.left.flatMap(allTypedVars) ++ prem.statement.right.flatMap(allTypedVars)
      val varsToChange: Map[Variable[Ind], TypedVariable] = 
        allvars.collect { case (v, typ) if v.id.no != typ.hashCode().abs => (v, mkTypedVar(v.id.name, typ)) }.toMap

      def changeVarInExpr[A](e: Expr[A]): Expr[A] = e match
        case v: Variable[?] =>
          varsToChange.toMap.getOrElse(v, v).asInstanceOf[Variable[A]]
        case Abs(v: Variable[?], body) =>
          val targetVar = varsToChange.toMap.getOrElse(v, v)
          val targetBody = changeVarInExpr(body) 
          if (targetVar eq v) && (targetBody eq body) then e else
          Abs(targetVar, targetBody).asInstanceOf[Expr[A]]
        case App(func, arg) =>
          val targetFunc = changeVarInExpr(func)
          val targetArg = changeVarInExpr(arg)
          if (targetFunc eq func ) && (targetArg eq arg) then e else
          App(targetFunc, targetArg)
        case cst: Constant[A] => cst
      val targetSequent = prem.statement.left.map(changeVarInExpr) |- prem.statement.right.map(changeVarInExpr)
      val instPrem = prem.of( (varsToChange.map { case (from, to) => from := to}).toSeq* )
      have(targetSequent) by Restate.from(instPrem)
    }

    def apply(using proof: Proof)(inst: Seq[(Variable[Ind], Expr[Ind])], prem: proof.Fact): proof.ProofTacticJudgement = TacticSubproof { ip ?=>
      val s1 = have(lisa.hol.HOLSteps._INST_TYPE(inst, prem))
      have(variableTypesNames(s1))
    }

  }
}

/*
prelForm.underlying:    app(app(=:=(Pi(Pi(A)(lambda(x, B)))(lambda(x, 𝔹))))(app(=:=(Pi(A)(lambda(x, B))))(z)))(app(abs(Pi(A)(lambda(x, B)))(lambda(x, abs(Pi(A)(lambda(x, B)))(lambda(y, app(app(=:=(Pi(A)(lambda(x, B))))(x))(y))))))(z)) === One
targetForm.underlying:  app(app(=:=(Pi(Pi(A)(lambda(x_196788543, B)))(lambda(x_196788543, 𝔹))))(app(=:=(Pi(A)(lambda(x_196788543, B))))(z_196788543)))(app(abs(Pi(A)(lambda(x_196788543, B)))(lambda(x_196788543, abs(Pi(A)(lambda(x_196788543, B)))(lambda(y_196788543, app(app(=:=(Pi(A)(lambda(x_196788543, B))))(x_196788543))(y_196788543))))))(z_196788543)) === One
*/