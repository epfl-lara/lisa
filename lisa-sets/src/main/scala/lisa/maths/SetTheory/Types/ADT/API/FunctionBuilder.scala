package lisa.maths.SetTheory.Types.ADT.API

import lisa.maths.SetTheory.SetTheory._
import lisa.maths.SetTheory.Types.ADT.PatternMatching.semantics.PatternSystem
import lisa.maths.SetTheory.Types.ADT.PatternMatching.syntax.CaseAccumulator
import lisa.maths.SetTheory.Types.ADT.interface.ADT
import lisa.maths.SetTheory.Types.ADT.interface.ADTFunction
import lisa.maths.SetTheory.Types.ADT.interface.RecFunction
import lisa.maths.SetTheory.Types.ADT.interface.SpecializedADT
import lisa.maths.SetTheory.Types.ADT.recursion.SemanticFunction
import lisa.maths.SetTheory.Types.ADT.support.InterfaceHelpers.substitutionsFromArgs

private def buildFunction[S: Sort](parameters: Seq[Variable[Ind]], adt: SpecializedADT[?], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: CaseAccumulator[Expr[Ind], Unit] ?=> Unit
): ADTFunction[S] = {
  val builder = CaseAccumulator[Expr[Ind], Unit](())
  cases(using builder)
  val patterns = builder.compile(adt, body => parameters ++ Seq(returnType, body)).fold(msg => throw new IllegalArgumentException(msg), identity)
  val caseExpressions = patterns.clauses.flatMap(p => p.binders ++ Seq(p.inputTerm, p.body, p.branchPremise))
  val self = Variable[Ind](freshId(parameters ++ Seq(adt.term, returnType) ++ caseExpressions, s"${name.value}RecSelf"))
  defineFunction[S](parameters, adt, returnType, self, patterns)
}

private def buildRecursiveFunction[S: Sort](parameters: Seq[Variable[Ind]], adt: SpecializedADT[?], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: Expr[Ind] => (CaseAccumulator[Expr[Ind], Unit] ?=> Unit)
): RecFunction[S] = {
  val builder = CaseAccumulator[Expr[Ind], Unit](())
  val self = Variable[Ind](freshId(parameters ++ Seq(adt.term, returnType), s"${name.value}RecSelf"))
  cases(self)(using builder)
  val patterns = builder.compile(adt, body => parameters ++ Seq(returnType, self, body)).fold(msg => throw new IllegalArgumentException(msg), identity)
  defineFunction[S](parameters, adt, returnType, self, patterns)
}

private def defineFunction[S: Sort](
    parameters: Seq[Variable[Ind]],
    adt: SpecializedADT[?],
    returnType: Expr[Ind],
    self: Variable[Ind],
    patterns: PatternSystem[Expr[Ind]]
)(using name: sourcecode.Name): ADTFunction[S] = {
  val substitutions = substitutionsFromArgs("ADT", adt.base.name, adt.base.typeVariablesSeq, adt.typeArgs)
    .filter(substitution => substitution._2 != substitution._1)
  val semantic = new SemanticFunction(name.value, parameters, adt.base.semantic, adt.term, substitutions, self, patterns, returnType)
  new ADTFunction[S](semantic, adt.base)
}

/**
 * Defines a function using the generic ADT's parameters.
 */
def fun[S: Sort](adt: ADT[S], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: CaseAccumulator[Expr[Ind], Unit] ?=> Unit
): ADTFunction[S] =
  buildFunction[S](adt.typeVariablesSeq, new SpecializedADT(adt, adt.typeVariablesSeq), returnType)(cases)

/**
 * Defines a function on a specialized domain without parameters.
 */
def fun(adt: SpecializedADT[?], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: CaseAccumulator[Expr[Ind], Unit] ?=> Unit
): ADTFunction[Ind] =
  buildFunction[Ind](Seq.empty, adt, returnType)(cases)

/**
 * Defines a function with 1 explicit parameter in the supplied order.
 */
def fun(parameters: Variable[Ind])(adt: SpecializedADT[?], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: CaseAccumulator[Expr[Ind], Unit] ?=> Unit
): ADTFunction[Ind >>: Ind] =
  buildFunction[Ind >>: Ind](Seq(parameters), adt, returnType)(cases)

/**
 * Defines a function with 2 explicit parameters in the supplied order.
 */
def fun(parameters: (Variable[Ind], Variable[Ind]))(adt: SpecializedADT[?], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: CaseAccumulator[Expr[Ind], Unit] ?=> Unit
): ADTFunction[Ind >>: Ind >>: Ind] =
  buildFunction[Ind >>: Ind >>: Ind](Seq(parameters._1, parameters._2), adt, returnType)(cases)

/**
 * Defines a function with 3 explicit parameters in the supplied order.
 */
def fun(parameters: (Variable[Ind], Variable[Ind], Variable[Ind]))(adt: SpecializedADT[?], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: CaseAccumulator[Expr[Ind], Unit] ?=> Unit
): ADTFunction[Ind >>: Ind >>: Ind >>: Ind] =
  buildFunction[Ind >>: Ind >>: Ind >>: Ind](Seq(parameters._1, parameters._2, parameters._3), adt, returnType)(cases)

/**
 * Defines a function with 4 explicit parameters in the supplied order.
 */
def fun(parameters: (Variable[Ind], Variable[Ind], Variable[Ind], Variable[Ind]))(adt: SpecializedADT[?], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: CaseAccumulator[Expr[Ind], Unit] ?=> Unit
): ADTFunction[Ind >>: Ind >>: Ind >>: Ind >>: Ind] =
  buildFunction[Ind >>: Ind >>: Ind >>: Ind >>: Ind](Seq(parameters._1, parameters._2, parameters._3, parameters._4), adt, returnType)(cases)

/**
 * Defines a function with 5 explicit parameters in the supplied order.
 */
def fun(parameters: (Variable[Ind], Variable[Ind], Variable[Ind], Variable[Ind], Variable[Ind]))(adt: SpecializedADT[?], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: CaseAccumulator[Expr[Ind], Unit] ?=> Unit
): ADTFunction[Ind >>: Ind >>: Ind >>: Ind >>: Ind >>: Ind] =
  buildFunction[Ind >>: Ind >>: Ind >>: Ind >>: Ind >>: Ind](Seq(parameters._1, parameters._2, parameters._3, parameters._4, parameters._5), adt, returnType)(cases)

/**
 * Defines a recursive function using the generic ADT's parameters.
 */
def recFun[S: Sort](adt: ADT[S], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: Expr[Ind] => (CaseAccumulator[Expr[Ind], Unit] ?=> Unit)
): RecFunction[S] =
  buildRecursiveFunction[S](adt.typeVariablesSeq, new SpecializedADT(adt, adt.typeVariablesSeq), returnType)(cases)

/**
 * Defines a recursive function on a specialized domain without parameters.
 */
def recFun(adt: SpecializedADT[?], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: Expr[Ind] => (CaseAccumulator[Expr[Ind], Unit] ?=> Unit)
): RecFunction[Ind] =
  buildRecursiveFunction[Ind](Seq.empty, adt, returnType)(cases)

/**
 * Defines a recursive function with 1 explicit parameter in the supplied order.
 */
def recFun(parameters: Variable[Ind])(adt: SpecializedADT[?], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: Expr[Ind] => (CaseAccumulator[Expr[Ind], Unit] ?=> Unit)
): RecFunction[Ind >>: Ind] =
  buildRecursiveFunction[Ind >>: Ind](Seq(parameters), adt, returnType)(cases)

/**
 * Defines a recursive function with 2 explicit parameters in the supplied order.
 */
def recFun(parameters: (Variable[Ind], Variable[Ind]))(adt: SpecializedADT[?], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: Expr[Ind] => (CaseAccumulator[Expr[Ind], Unit] ?=> Unit)
): RecFunction[Ind >>: Ind >>: Ind] =
  buildRecursiveFunction[Ind >>: Ind >>: Ind](Seq(parameters._1, parameters._2), adt, returnType)(cases)

/**
 * Defines a recursive function with 3 explicit parameters in the supplied order.
 */
def recFun(parameters: (Variable[Ind], Variable[Ind], Variable[Ind]))(adt: SpecializedADT[?], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: Expr[Ind] => (CaseAccumulator[Expr[Ind], Unit] ?=> Unit)
): RecFunction[Ind >>: Ind >>: Ind >>: Ind] =
  buildRecursiveFunction[Ind >>: Ind >>: Ind >>: Ind](Seq(parameters._1, parameters._2, parameters._3), adt, returnType)(cases)

/**
 * Defines a recursive function with 4 explicit parameters in the supplied order.
 */
def recFun(parameters: (Variable[Ind], Variable[Ind], Variable[Ind], Variable[Ind]))(adt: SpecializedADT[?], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: Expr[Ind] => (CaseAccumulator[Expr[Ind], Unit] ?=> Unit)
): RecFunction[Ind >>: Ind >>: Ind >>: Ind >>: Ind] =
  buildRecursiveFunction[Ind >>: Ind >>: Ind >>: Ind >>: Ind](Seq(parameters._1, parameters._2, parameters._3, parameters._4), adt, returnType)(cases)

/**
 * Defines a recursive function with 5 explicit parameters in the supplied order.
 */
def recFun(parameters: (Variable[Ind], Variable[Ind], Variable[Ind], Variable[Ind], Variable[Ind]))(adt: SpecializedADT[?], returnType: Expr[Ind])(using
    name: sourcecode.Name
)(
    cases: Expr[Ind] => (CaseAccumulator[Expr[Ind], Unit] ?=> Unit)
): RecFunction[Ind >>: Ind >>: Ind >>: Ind >>: Ind >>: Ind] =
  buildRecursiveFunction[Ind >>: Ind >>: Ind >>: Ind >>: Ind >>: Ind](Seq(parameters._1, parameters._2, parameters._3, parameters._4, parameters._5), adt, returnType)(cases)
