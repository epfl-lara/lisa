package lisa.maths.SetTheory.Types.ADTv2.API

import lisa.maths.SetTheory.Types.ADTv2.encoding.ADT
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

def recFun[N <: Arity](
  using name: sourcecode.Name
)(
  adt: ADT[N], returnType: Expr[Ind]
)(
    cases: Expr[Ind] => (CaseAccumulator[N, Expr[Ind], Unit] ?=> Unit)
): recursion.RecFunction[N] = {
  val builder = CaseAccumulator[N, Expr[Ind], Unit](())
  val self = recursion.RecFunction.selfPlaceholder(name.value)
  cases(self)(using builder)

  builder.isValid(adt) match
    case None =>
      recursion.RecFunction[N](
        name.value,
        adt,
        self,
        builder.build.map((k, v) => (k.semantic, v)),
        returnType
      )
    case Some(msg) => throw new IllegalArgumentException(msg)
}

def recFun[N <: Arity](adt: ADT[N], returnADT: ADT[N])(using name: sourcecode.Name
)(
  cases: Expr[Ind] => (CaseAccumulator[N, Expr[Ind], Unit] ?=> Unit)
): recursion.RecFunction[N] =
  recFun[N](adt, returnADT.semantic.term(Seq.empty))(cases)