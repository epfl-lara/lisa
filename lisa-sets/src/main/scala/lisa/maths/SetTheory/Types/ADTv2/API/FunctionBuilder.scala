package lisa.maths.SetTheory.Types.ADTv2.API

import lisa.maths.SetTheory.Types.ADTv2.interface.{ADT, RecFunction}
import lisa.maths.SetTheory.Types.ADTv2.functions.*
import lisa.maths.SetTheory.Types.ADTv2.recursion

import lisa.maths.SetTheory.SetTheory.{*, given}
import lisa.utils.prooflib.ProofTacticLib.Arity


def fun[N <: Arity](adt: ADT[N], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(cases: CaseAccumulator[N, Expr[Ind], Unit] ?=> Unit): ADTFunction[N] = {
  val builder = CaseAccumulator[N, Expr[Ind], Unit](())
  cases(using builder)
  builder.isValid(adt) match
    case None => ADTFunction(
        SemanticFunction[N](
          name.value,
          adt.semantic,
          builder.build.map((k, v) => (k.semantic, v)),
          returnType
        ),
        adt
      )
    case Some(msg) => throw new IllegalArgumentException(msg)
}

def fun[N <: Arity](adt: ADT[N], returnADT: ADT[N])(
  using name: sourcecode.Name
)(cases: CaseAccumulator[N, Expr[Ind], Unit] ?=> Unit): ADTFunction[N] =
  fun[N](adt, returnADT.semantic.term(Seq.empty))(cases)

/** Second version of REC ------------------------------------------------- */

def recFun2[N <: Arity](adt: ADT[N], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: Expr[Ind] => (CaseAccumulator[N, Expr[Ind], Unit] ?=> Unit)
): RecFunction[N] = {
  val builder = CaseAccumulator[N, Expr[Ind], Unit](())
  val self = RecFunction.selfPlaceholder(name.value)
  cases(self)(using builder)

  builder.isValid(adt) match
    case None =>
      val semantic = recursion.RecFunSemantics[N](
        name.value,
        adt.semantic,
        self,
        builder.build.map((k, v) => (k.semantic, v)),
        returnType
      )
      new RecFunction[N](semantic, adt)
    case Some(msg) => throw new IllegalArgumentException(msg)
}

def recFun2[N <: Arity](adt: ADT[N], returnADT: ADT[N])(using name: sourcecode.Name
)(
  cases: Expr[Ind] => (CaseAccumulator[N, Expr[Ind], Unit] ?=> Unit)
): RecFunction[N] =
  recFun2[N](adt, returnADT.semantic.term(Seq.empty))(cases)
