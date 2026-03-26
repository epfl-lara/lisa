import lisa.maths.SetTheory.Types.ADTv2.*

object Other extends lisa.Main {

  // *******************************
  // *   Other ADTv2 Examples...   *
  // *******************************



  // **********************
  // * TypeChecker Tactic *
  // **********************
  
  val typeA_1 = TypeRef("A")
  val typeA_2 = Variable[Ind]("A")
  val x = Variable[Ind]("x")
  val l = Variable[Ind]("l")

  // Lemma(nil(typeA_1) :: list(typeA_1)) {
  //   have(thesis) by TypeChecker.prove
  // }
  // Lemma((x :: typeA_2, l :: list(typeA_1)) |- cons(typeA_1) * x * l :: list(typeA_1)) {
  //   have(thesis) by TypeChecker.prove
  // }

  // *****************
  // *  Arity Tests  *
  // *****************

  // println("Printing arity for cons:")
  // println(s"\tspecification: ${consSpec.arity()}")
  // println(s"\tsyntactic: ${consSyntactic.arity}")
  // println(s"\tsemantic: ${consSemantic.arity}")
  // println(s"\tfinal: ${cons.arity}")
  // TODO: fix this arity mismatch

  // ********************
  // *  Variable Names  *
  // ********************

  // section("Variable Name Examples")

  // val a = variable[Ind]
  // val v = variable[Ind]
  // val uv1 = UniqueVariable("v")
  // val uv2 = UniqueVariable("v")
  // UniqueVariable.saveExistingVariables(a)
  // val uv3 = UniqueVariable("a")

  // println(s"Variable v: $v")
  // println(s"UniqueVariable uv1: $uv1")
  // println(s"UniqueVariable uv2: $uv2")
  // println(s"UniqueVariable uv3: $uv3")
  // println(s"Equality checks: uv1 == uv2: ${uv1 == uv2}, uv3 == a: ${uv3 == a}")
  // println(s"Equation : ${forall(v, uv1 === v)}")
  // println(s"Equation : ${forall(uv2, uv1 === uv2)}")

}