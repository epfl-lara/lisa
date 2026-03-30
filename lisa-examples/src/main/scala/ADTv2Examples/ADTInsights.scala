import lisa.utils.collection.VecSet.empty
import lisa.maths.SetTheory.Functions.Pi.{->:}

object ADTInsights extends lisa.Main {

  // draft()
  // withCache()


  import lisa.maths.SetTheory.Types.ADTv2
  import lisa.maths.SetTheory.Types.ADTv2.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.ADTSpec
  import lisa.maths.SetTheory.Types.ADTv2.encoding.*
  import lisa.maths.SetTheory.Types.ADTv2.support.UsefulTheorems.funEqDef

  import lisa.maths.SetTheory.SetTheory.{*, given}
  import lisa.maths.SetTheory.Base.Singleton
  import lisa.maths.SetTheory.Functions.Function.functionBetween
  import lisa.maths.SetTheory.Functions.BasicTheorems.{appTyping, funcBetweenEqInFuncSpace}

  // ************************************
  // * ADTv2 Test: Syntax Tree Creation *
  // ************************************

  val nilSpec = constructor("nil")
  val consSpec = constructor("cons", "A", SelfRef)
  val listSpec = adt(
    name = "list",
    typeParameters = Seq("A"),
    constructors = Seq(nilSpec, consSpec)
  )

  

  // println(s"List spec: ${listSpec}")
  // println(s"Tree spec: ${treeSpec}")
  // println(" ")

  // ************************
  // * SyntacticConstructor *
  // ************************

  // section("Syntactic Constructors")

  val nilSyntactic = new SyntacticConstructor(
    specification = nilSpec.args,
    variables1 = Seq.empty,
    variables2 = Seq.empty
  )
  val consSyntactic = new SyntacticConstructor(
    specification = consSpec.args,
    variables1 = Seq(Variable[Ind]("head"), Variable[Ind]("tail")),
    variables2 = Seq(Variable[Ind]("head2"), Variable[Ind]("tail2"))
  )
  // show(nilSyntactic.injectivity)
  // show(consSyntactic.injectivity)

  // ****************
  // * SyntacticADT *
  // ****************

  section("Syntactic ADT")

  val varSeq = Seq(Variable[Ind]("A")).asInstanceOf[Variable[Ind] ** 1]
  val listSyntactic = new SyntacticADT(
    name = "list",
    constructors = Seq(consSyntactic, nilSyntactic),
    typeVariables = varSeq
  )
  show(listSyntactic.induction)
  // show(listSyntactic.injectivity(consSyntactic, nilSyntactic))

  // ***********************
  // * SemanticConstructor *
  // ***********************

  // section("Semantic Constructors")

  val nilSemantic = new SemanticConstructor("nil", nilSyntactic, listSyntactic)
  val consSemantic = new SemanticConstructor("cons", consSyntactic, listSyntactic)

  // show(nilSemantic.shortDefinition)
  // show(consSemantic.shortDefinition)
  // show(nilSemantic.injectivity)
  // show(consSemantic.injectivity)
  // show(nilSemantic.intro)
  // show(consSemantic.intro)
  // println(s"ind case : ${consSemantic.inductiveCase}")
  // println(s"cons term: ${consSemantic.term(consSemantic.typeVariablesSeq)}")
  // println(s"cons appliedTerm: ${consSemantic.appliedTerm(consSemantic.variables)}")

  // ***************
  // * SemanticADT *
  // ***************

  section("Semantic ADT")

  val listSemantic =
    new SemanticADT(listSyntactic, constructors = Seq(consSemantic, nilSemantic))

  show(listSemantic.injectivity(consSemantic, nilSemantic))
  show(listSemantic.induction)
  show(listSemantic.elim)

  // *************************************
  // *  Final Constuctor and ADT classes *
  // *************************************

  section("Final ADT and Constructor Classes")

  val nil = Constructor(nilSemantic)
  val cons = Constructor(consSemantic)
  val list = ADT(listSemantic, Seq(cons, nil))

  // show(cons.injectivity)
  // show(nil.injectivity)
  // show(cons.intro)
  // show(nil.intro)
  show(list.induction)
  show(list.elim)
  show(list.injectivity(cons, nil))

}
