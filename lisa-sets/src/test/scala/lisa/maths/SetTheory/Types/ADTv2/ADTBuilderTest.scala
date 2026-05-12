package lisa.maths.SetTheory.Types.ADTv2

import org.scalatest.funsuite.AnyFunSuite

class ADTBuilderTest extends AnyFunSuite with lisa.TestMain {

  given lib: lisa.SetTheoryLibrary.type = lisa.SetTheoryLibrary

  import lisa.maths.SetTheory.SetTheory.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.{*, given}
  import lisa.maths.SetTheory.Types.ADTv2.syntax.AST.SelfRef

  test("monomorphic ADT exposes injectivity and induction theorems") {
    val boolDemo = adt(
      name = "boolBuilderTest",
      constructors = Seq(
        ("tru", Seq.empty),
        ("fals", Seq.empty)
      )
    )
    val truDemo = boolDemo.constructors(0)
    val falsDemo = boolDemo.constructors(1)

    Theorem(() |- !(truDemo === falsDemo)) {
      have(thesis) by Tautology.from(boolDemo.injectivity(truDemo, falsDemo))
    }

    assert(boolDemo.typeVariablesSeq.isEmpty)
  }

  test("builder overloads create expected arities") {
    val noTypeArg = adt(
      name = "noTypeArgBuilderTest",
      constructors = Seq(("single", Seq.empty))
    )
    val oneTypeArg = adt(
      name = "oneTypeArgBuilderTest",
      typeVars = "A",
      constructors = Seq(("wrap", Seq(("value", "A"))))
    )
    val twoTypeArgs = adt(
      name = "twoTypeArgsBuilderTest",
      typeVars = ("A", "B"),
      constructors = Seq(("pair", Seq(("left", "A"), ("right", "B"))))
    )
    val runtimeTypeArgs = adt(
      name = "runtimeTypeArgsBuilderTest",
      typeVars = Seq("A", "B", "C"),
      constructors = Seq(("triple", Seq(("x", "A"), ("y", "B"), ("z", "C"))))
    )

    assert(noTypeArg.typeVariablesSeq.size == 0)
    assert(oneTypeArg.typeVariablesSeq.size == 1)
    assert(twoTypeArgs.typeVariablesSeq.size == 2)
    assert(runtimeTypeArgs.typeVariablesSeq.size == 3)
  }

  test("builder rejects duplicate type variables") {
    assertThrows[IllegalArgumentException] {
      adt(
        name = "duplicateTypeVariablesBuilderTest",
        typeVars = Seq("A", "A"),
        constructors = Seq(("wrap", Seq(("value", "A"))))
      )
    }
  }

  test("builder rejects reserved constructor argument names") {
    assertThrows[IllegalArgumentException] {
      adt(
        name = "reservedArgumentBuilderTest",
        typeVars = "A",
        constructors = Seq(("wrap", Seq(("n", "A"))))
      )
    }
  }

  test("builder rejects unsupported runtime arity") {
    assertThrows[IllegalArgumentException] {
      adt(
        name = "unsupportedArityBuilderTest",
        typeVars = Seq("A", "B", "C", "D", "E", "F"),
        constructors = Seq(("mk", Seq.empty))
      )
    }
  }
}
