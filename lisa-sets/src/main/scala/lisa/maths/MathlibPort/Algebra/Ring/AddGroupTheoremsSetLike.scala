package lisa.maths.MathlibPort.Algebra.Ring

import lisa.maths.SetTheory.Base.Predef.{_, given}
import lisa.maths.SetTheory.Functions
import lisa.maths.SetTheory.Functions.Predef.{_, given}

/**
 * Set-based additive-group theorems for the predicates in [[Defs]].
 */
object AddGroupTheoremsSetLike extends lisa.Main {

  val R = variable[Ind]
  val add = variable[Ind]
  val zero = variable[Ind]
  val negOp = variable[Ind]

  val x = variable[Ind]
  val y = variable[Ind]

  private def addApp(a: Expr[Ind], b: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(add)((a, b))

  private def negApp(a: Expr[Ind]): Expr[Ind] =
    Functions.Function.app(negOp)(a)

  extension (a: Expr[Ind]) {
    infix def +(b: Expr[Ind]): Expr[Ind] = addApp(a, b)
    def negOf: Expr[Ind] = negApp(a)
  }

  val addMonoid_of_addGroup = Theorem(
    Defs.addGroup(R)(add)(zero)(negOp) |- Defs.addMonoid(R)(add)(zero)
  ) {
    have(thesis) by Tautology.from(Defs.addGroup.definition)
  }

  val addSemigroup_of_addMonoid = Theorem(
    Defs.addMonoid(R)(add)(zero) |- Defs.addSemigroup(R)(add)
  ) {
    have(thesis) by Tautology.from(Defs.addMonoid.definition)
  }

  val hasAdd_of_addSemigroup = Theorem(
    Defs.addSemigroup(R)(add) |- Defs.hasAdd(R)(add)
  ) {
    have(thesis) by Tautology.from(Defs.addSemigroup.definition)
  }

  val hasAdd_of_addGroup = Theorem(
    Defs.addGroup(R)(add)(zero)(negOp) |- Defs.hasAdd(R)(add)
  ) {
    have(thesis) by Tautology.from(addMonoid_of_addGroup, addSemigroup_of_addMonoid, hasAdd_of_addSemigroup)
  }

  val zero_mem_of_addMonoid = Theorem(
    Defs.addMonoid(R)(add)(zero) |- zero ∈ R
  ) {
    have(thesis) by Tautology.from(Defs.addMonoid.definition, Defs.hasZero.definition)
  }

  val add_closed = Theorem(
    (Defs.hasAdd(R)(add), x ∈ R, y ∈ R) |- (x + y) ∈ R
  ) {
    have(thesis) by Tautology.from(
      Defs.hasAdd.definition,
      Functions.BasicTheorems.appTyping of (f := add, A := (R × R), B := R, x := (x, y)),
      CartesianProduct.membershipSufficientCondition of (A := R, B := R, x := x, y := y)
    )
  }

  val hasNeg_of_addGroup = Theorem(
    Defs.addGroup(R)(add)(zero)(negOp) |- Defs.hasNeg(R)(negOp)
  ) {
    have(thesis) by Tautology.from(Defs.addGroup.definition)
  }

  val neg_mem_of_addGroup = Theorem(
    Defs.addGroup(R)(add)(zero)(negOp) |- forall(x, (x ∈ R) ==> (x.negOf ∈ R))
  ) {
    assume(Defs.addGroup(R)(add)(zero)(negOp))
    have(Defs.hasNeg(R)(negOp)) by Tautology.from(hasNeg_of_addGroup)
    thenHave(negOp :: R -> R) by Substitute(Defs.hasNeg.definition)
    thenHave(x ∈ R |- x.negOf ∈ R) by Tautology.fromLastStep(
      Functions.BasicTheorems.appTyping of (f := negOp, A := R, B := R, x := x)
    )
    thenHave((x ∈ R) ==> (x.negOf ∈ R)) by RightImplies
    thenHave(thesis) by RightForall
  }

  val left_zero_of_addMonoid = Theorem(
    Defs.addMonoid(R)(add)(zero) |- forall(x, (x ∈ R) ==> ((zero + x) === x))
  ) {
    have(thesis) by Tautology.from(Defs.addMonoid.definition, Defs.leftZero.definition)
  }

  val right_zero_of_addMonoid = Theorem(
    Defs.addMonoid(R)(add)(zero) |- forall(x, (x ∈ R) ==> ((x + zero) === x))
  ) {
    have(thesis) by Tautology.from(Defs.addMonoid.definition, Defs.rightZero.definition)
  }

  val left_neg_of_addGroup = Theorem(
    Defs.addGroup(R)(add)(zero)(negOp) |- forall(x, (x ∈ R) ==> ((x.negOf + x) === zero))
  ) {
    have(thesis) by Tautology.from(Defs.addGroup.definition, Defs.leftNeg.definition)
  }

  val right_neg_of_addGroup = Theorem(
    Defs.addGroup(R)(add)(zero)(negOp) |- forall(x, (x ∈ R) ==> ((x + x.negOf) === zero))
  ) {
    have(thesis) by Tautology.from(Defs.addGroup.definition, Defs.rightNeg.definition)
  }
}

