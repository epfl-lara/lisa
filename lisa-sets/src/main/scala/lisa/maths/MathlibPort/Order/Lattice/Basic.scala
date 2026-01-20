package lisa.maths.MathlibPort.Order.Lattice

/**
 * mathlib port (re-development) sketch.
 *
 * Lean source reference: `Mathlib/Order/Lattice/Basic`.
 *
 * This file develops the usual lattice laws from order-theoretic characterizations
 * of `sup` and `inf` (least upper bounds / greatest lower bounds).
 */
object Basic extends lisa.Main {

  val x = variable[Ind]
  val y = variable[Ind]
  val z = variable[Ind]

  val le = variable[Ind >>: Ind >>: Prop]
  val sup = variable[Ind >>: Ind >>: Ind]
  val inf = variable[Ind >>: Ind >>: Ind]

  extension (a: Expr[Ind]) {
    infix def ≤(b: Expr[Ind]): Expr[Prop] = App(App(le, a), b)
    infix def ⊔(b: Expr[Ind]): Expr[Ind] = App(App(sup, a), b)
    infix def ⊓(b: Expr[Ind]): Expr[Ind] = App(App(inf, a), b)
  }

  val le_refl = forall(x, x ≤ x)
  val le_antisymm = forall(x, forall(y, ((x ≤ y) /\ (y ≤ x)) ==> (x === y)))
  val le_trans = forall(x, forall(y, forall(z, ((x ≤ y) /\ (y ≤ z)) ==> (x ≤ z))))

  val sup_lub = forall(x, forall(y, forall(z, ((x ≤ z) /\ (y ≤ z)) <=> ((x ⊔ y) ≤ z))))
  val inf_glb = forall(x, forall(y, forall(z, ((z ≤ x) /\ (z ≤ y)) <=> (z ≤ (x ⊓ y)))))

  val sup_lower_bounds = Theorem((le_refl, sup_lub) |- (x ≤ (x ⊔ y)) /\ (y ≤ (x ⊔ y))) {
    val refl = assume(le_refl)
    val lub = assume(sup_lub)

    val s1 = have(((x ≤ (x ⊔ y)) /\ (y ≤ (x ⊔ y))) <=> ((x ⊔ y) ≤ (x ⊔ y))) by Tautology.from(
      lub of (x := x, y := y, z := (x ⊔ y))
    )
    val s2 = have((x ⊔ y) ≤ (x ⊔ y)) by Tautology.from(refl of (x := (x ⊔ y)))
    have(thesis) by Tautology.from(s1, s2)
  }

  val inf_upper_bounds = Theorem((le_refl, inf_glb) |- ((x ⊓ y) ≤ x) /\ ((x ⊓ y) ≤ y)) {
    val refl = assume(le_refl)
    val glb = assume(inf_glb)

    val s1 = have((((x ⊓ y) ≤ x) /\ ((x ⊓ y) ≤ y)) <=> ((x ⊓ y) ≤ (x ⊓ y))) by Tautology.from(
      glb of (x := x, y := y, z := (x ⊓ y))
    )
    val s2 = have((x ⊓ y) ≤ (x ⊓ y)) by Tautology.from(refl of (x := (x ⊓ y)))
    have(thesis) by Tautology.from(s1, s2)
  }

  val sup_comm = Theorem((le_refl, le_antisymm, sup_lub) |- ((x ⊔ y) === (y ⊔ x))) {
    val antisymm = assume(le_antisymm)
    val lub = assume(sup_lub)

    val s1 = have((x ⊔ y) ≤ (y ⊔ x)) by Tautology.from(
      lub of (x := x, y := y, z := (y ⊔ x)),
      sup_lower_bounds of (x := y, y := x)
    )
    have(thesis) by Tautology.from(
      antisymm of (x := (x ⊔ y), y := (y ⊔ x)),
      s1,
      s1 of (x := y, y := x)
    )
  }

  val inf_comm = Theorem((le_refl, le_antisymm, inf_glb) |- ((x ⊓ y) === (y ⊓ x))) {
    val antisymm = assume(le_antisymm)
    val glb = assume(inf_glb)

    val s1 = have((x ⊓ y) ≤ (y ⊓ x)) by Tautology.from(
      glb of (x := y, y := x, z := (x ⊓ y)),
      inf_upper_bounds
    )
    have(thesis) by Tautology.from(
      antisymm of (x := (x ⊓ y), y := (y ⊓ x)),
      s1,
      s1 of (x := y, y := x)
    )
  }

  val sup_absorption = Theorem((le_refl, le_antisymm, sup_lub) |- (x ≤ y) ==> ((x ⊔ y) === y)) {
    val refl = assume(le_refl)
    val antisymm = assume(le_antisymm)
    val lub = assume(sup_lub)

    val hxy = assume(x ≤ y)
    val s1 = have((x ⊔ y) ≤ y) by Tautology.from(
      lub of (x := x, y := y, z := y),
      hxy,
      refl of (x := y)
    )
    val s2 = have(y ≤ (x ⊔ y)) by Tautology.from(sup_lower_bounds of (x := x, y := y))
    have((x ⊔ y) === y) by Tautology.from(
      antisymm of (x := (x ⊔ y), y := y),
      s1,
      s2
    )
    thenHave(thesis) by RightImplies
  }

  val inf_absorption = Theorem((le_refl, le_antisymm, inf_glb) |- (x ≤ y) ==> ((x ⊓ y) === x)) {
    val refl = assume(le_refl)
    val antisymm = assume(le_antisymm)
    val glb = assume(inf_glb)

    val hxy = assume(x ≤ y)
    val s1 = have((x ⊓ y) ≤ x) by Tautology.from(inf_upper_bounds)
    val s2 = have(x ≤ (x ⊓ y)) by Tautology.from(
      glb of (x := x, y := y, z := x),
      refl of (x := x),
      hxy
    )
    have((x ⊓ y) === x) by Tautology.from(
      antisymm of (x := (x ⊓ y), y := x),
      s1,
      s2
    )
    thenHave(thesis) by RightImplies
  }

  val sup_idem = Theorem((le_refl, le_antisymm, sup_lub) |- ((x ⊔ x) === x)) {
    val refl = assume(le_refl)
    val antisymm = assume(le_antisymm)
    val lub = assume(sup_lub)

    val s1 = have((x ⊔ x) ≤ x) by Tautology.from(
      lub of (x := x, y := x, z := x),
      refl of (x := x)
    )
    val s2 = have(x ≤ (x ⊔ x)) by Tautology.from(sup_lower_bounds of (x := x, y := x))
    have(thesis) by Tautology.from(
      antisymm of (x := (x ⊔ x), y := x),
      s1,
      s2
    )
  }

  val inf_idem = Theorem((le_refl, le_antisymm, inf_glb) |- ((x ⊓ x) === x)) {
    val refl = assume(le_refl)
    val antisymm = assume(le_antisymm)
    val glb = assume(inf_glb)

    val s1 = have((x ⊓ x) ≤ x) by Tautology.from(inf_upper_bounds of (x := x, y := x))
    val s2 = have(x ≤ (x ⊓ x)) by Tautology.from(
      glb of (x := x, y := x, z := x),
      refl of (x := x)
    )
    have(thesis) by Tautology.from(
      antisymm of (x := (x ⊓ x), y := x),
      s1,
      s2
    )
  }

  val sup_assoc = Theorem((le_refl, le_antisymm, le_trans, sup_lub) |- ((x ⊔ (y ⊔ z)) === ((x ⊔ y) ⊔ z))) {
    val refl = assume(le_refl)
    val antisymm = assume(le_antisymm)
    val trans = assume(le_trans)
    val lub = assume(sup_lub)

    val left = x ⊔ (y ⊔ z)
    val right = (x ⊔ y) ⊔ z

    val xy_le_right = have((x ⊔ y) ≤ right) by Tautology.from(sup_lower_bounds of (x := (x ⊔ y), y := z))
    val x_le_xy = have(x ≤ (x ⊔ y)) by Tautology.from(sup_lower_bounds)
    val y_le_xy = have(y ≤ (x ⊔ y)) by Tautology.from(sup_lower_bounds)
    val z_le_right = have(z ≤ right) by Tautology.from(sup_lower_bounds of (x := (x ⊔ y), y := z))

    val x_le_right = have(x ≤ right) by Tautology.from(
      trans of (x := x, y := (x ⊔ y), z := right),
      x_le_xy,
      xy_le_right
    )
    val y_le_right = have(y ≤ right) by Tautology.from(
      trans of (x := y, y := (x ⊔ y), z := right),
      y_le_xy,
      xy_le_right
    )
    val yz_le_right = have((y ⊔ z) ≤ right) by Tautology.from(
      lub of (x := y, y := z, z := right),
      y_le_right,
      z_le_right
    )

    val left_le_right = have(left ≤ right) by Tautology.from(
      lub of (x := x, y := (y ⊔ z), z := right),
      x_le_right,
      yz_le_right
    )

    val x_le_left = have(x ≤ left) by Tautology.from(sup_lower_bounds of (x := x, y := (y ⊔ z)))
    val yz_le_left = have((y ⊔ z) ≤ left) by Tautology.from(sup_lower_bounds of (x := x, y := (y ⊔ z)))
    val y_le_yz = have(y ≤ (y ⊔ z)) by Tautology.from(sup_lower_bounds of (x := y, y := z))
    val z_le_yz = have(z ≤ (y ⊔ z)) by Tautology.from(sup_lower_bounds of (x := y, y := z))

    val y_le_left = have(y ≤ left) by Tautology.from(
      trans of (x := y, y := (y ⊔ z), z := left),
      y_le_yz,
      yz_le_left
    )
    val z_le_left = have(z ≤ left) by Tautology.from(
      trans of (x := z, y := (y ⊔ z), z := left),
      z_le_yz,
      yz_le_left
    )
    val xy_le_left = have((x ⊔ y) ≤ left) by Tautology.from(
      lub of (x := x, y := y, z := left),
      x_le_left,
      y_le_left
    )
    val right_le_left = have(right ≤ left) by Tautology.from(
      lub of (x := (x ⊔ y), y := z, z := left),
      xy_le_left,
      z_le_left
    )

    have(thesis) by Tautology.from(
      antisymm of (x := left, y := right),
      left_le_right,
      right_le_left
    )
  }

  val inf_assoc = Theorem((le_refl, le_antisymm, le_trans, inf_glb) |- ((x ⊓ (y ⊓ z)) === ((x ⊓ y) ⊓ z))) {
    val antisymm = assume(le_antisymm)
    val trans = assume(le_trans)
    val glb = assume(inf_glb)

    val left = x ⊓ (y ⊓ z)
    val right = (x ⊓ y) ⊓ z

    val left_le_x = have(left ≤ x) by Tautology.from(inf_upper_bounds of (x := x, y := (y ⊓ z)))
    val left_le_yz = have(left ≤ (y ⊓ z)) by Tautology.from(inf_upper_bounds of (x := x, y := (y ⊓ z)))
    val yz_le_y = have((y ⊓ z) ≤ y) by Tautology.from(inf_upper_bounds of (x := y, y := z))
    val yz_le_z = have((y ⊓ z) ≤ z) by Tautology.from(inf_upper_bounds of (x := y, y := z))

    val left_le_y = have(left ≤ y) by Tautology.from(
      trans of (x := left, y := (y ⊓ z), z := y),
      left_le_yz,
      yz_le_y
    )
    val left_le_z = have(left ≤ z) by Tautology.from(
      trans of (x := left, y := (y ⊓ z), z := z),
      left_le_yz,
      yz_le_z
    )

    val left_le_xy = have(left ≤ (x ⊓ y)) by Tautology.from(
      glb of (x := x, y := y, z := left),
      left_le_x,
      left_le_y
    )
    val left_le_right = have(left ≤ right) by Tautology.from(
      glb of (x := (x ⊓ y), y := z, z := left),
      left_le_xy,
      left_le_z
    )

    val right_le_xy = have(right ≤ (x ⊓ y)) by Tautology.from(inf_upper_bounds of (x := (x ⊓ y), y := z))
    val right_le_z = have(right ≤ z) by Tautology.from(inf_upper_bounds of (x := (x ⊓ y), y := z))
    val xy_le_x = have((x ⊓ y) ≤ x) by Tautology.from(inf_upper_bounds of (x := x, y := y))
    val xy_le_y = have((x ⊓ y) ≤ y) by Tautology.from(inf_upper_bounds of (x := x, y := y))

    val right_le_x = have(right ≤ x) by Tautology.from(
      trans of (x := right, y := (x ⊓ y), z := x),
      right_le_xy,
      xy_le_x
    )
    val right_le_y = have(right ≤ y) by Tautology.from(
      trans of (x := right, y := (x ⊓ y), z := y),
      right_le_xy,
      xy_le_y
    )

    val right_le_yz = have(right ≤ (y ⊓ z)) by Tautology.from(
      glb of (x := y, y := z, z := right),
      right_le_y,
      right_le_z
    )
    val right_le_left = have(right ≤ left) by Tautology.from(
      glb of (x := x, y := (y ⊓ z), z := right),
      right_le_x,
      right_le_yz
    )

    have(thesis) by Tautology.from(
      antisymm of (x := left, y := right),
      left_le_right,
      right_le_left
    )
  }

  val sup_left_comm = Theorem((le_refl, le_antisymm, le_trans, sup_lub) |- ((x ⊔ (y ⊔ z)) === (y ⊔ (x ⊔ z)))) {
    val refl = assume(le_refl)
    val antisymm = assume(le_antisymm)
    val trans = assume(le_trans)
    val lub = assume(sup_lub)

    val assoc1 = have((x ⊔ (y ⊔ z)) === ((x ⊔ y) ⊔ z)) by Tautology.from(sup_assoc, refl, antisymm, trans, lub)
    val comm_xy = have((x ⊔ y) === (y ⊔ x)) by Tautology.from(sup_comm, refl, antisymm, lub)
    val cong1 = have(((x ⊔ y) ⊔ z) === ((y ⊔ x) ⊔ z)) by Congruence.from(comm_xy)
    val assoc2 = have((y ⊔ (x ⊔ z)) === ((y ⊔ x) ⊔ z)) by Tautology.from(
      sup_assoc of (x := y, y := x, z := z),
      refl,
      antisymm,
      trans,
      lub
    )
    val assoc2sym = have(((y ⊔ x) ⊔ z) === (y ⊔ (x ⊔ z))) by Congruence.from(assoc2)
    have(thesis) by Congruence.from(assoc1, cong1, assoc2sym)
  }

  val inf_left_comm = Theorem((le_refl, le_antisymm, le_trans, inf_glb) |- ((x ⊓ (y ⊓ z)) === (y ⊓ (x ⊓ z)))) {
    val refl = assume(le_refl)
    val antisymm = assume(le_antisymm)
    val trans = assume(le_trans)
    val glb = assume(inf_glb)

    val assoc1 = have((x ⊓ (y ⊓ z)) === ((x ⊓ y) ⊓ z)) by Tautology.from(inf_assoc, refl, antisymm, trans, glb)
    val comm_xy = have((x ⊓ y) === (y ⊓ x)) by Tautology.from(inf_comm, refl, antisymm, glb)
    val cong1 = have(((x ⊓ y) ⊓ z) === ((y ⊓ x) ⊓ z)) by Congruence.from(comm_xy)
    val assoc2 = have((y ⊓ (x ⊓ z)) === ((y ⊓ x) ⊓ z)) by Tautology.from(
      inf_assoc of (x := y, y := x, z := z),
      refl,
      antisymm,
      trans,
      glb
    )
    val assoc2sym = have(((y ⊓ x) ⊓ z) === (y ⊓ (x ⊓ z))) by Congruence.from(assoc2)
    have(thesis) by Congruence.from(assoc1, cong1, assoc2sym)
  }

  val topElem = variable[Ind]
  val botElem = variable[Ind]

  val le_top = forall(x, x ≤ topElem)
  val bot_le = forall(x, botElem ≤ x)

  val sup_bot = Theorem((le_refl, le_antisymm, sup_lub, bot_le) |- ((x ⊔ botElem) === x)) {
    val refl = assume(le_refl)
    val antisymm = assume(le_antisymm)
    val lub = assume(sup_lub)
    val botLe = assume(bot_le)

    val s1 = have((x ⊔ botElem) ≤ x) by Tautology.from(
      lub of (x := x, y := botElem, z := x),
      refl of (x := x),
      botLe of (x := x)
    )
    val s2 = have(x ≤ (x ⊔ botElem)) by Tautology.from(sup_lower_bounds of (x := x, y := botElem))
    have(thesis) by Tautology.from(
      antisymm of (x := (x ⊔ botElem), y := x),
      s1,
      s2
    )
  }

  val inf_top = Theorem((le_refl, le_antisymm, inf_glb, le_top) |- ((x ⊓ topElem) === x)) {
    val refl = assume(le_refl)
    val antisymm = assume(le_antisymm)
    val glb = assume(inf_glb)
    val leTop = assume(le_top)

    val s1 = have((x ⊓ topElem) ≤ x) by Tautology.from(inf_upper_bounds of (x := x, y := topElem))
    val s2 = have(x ≤ (x ⊓ topElem)) by Tautology.from(
      glb of (x := x, y := topElem, z := x),
      refl of (x := x),
      leTop of (x := x)
    )
    have(thesis) by Tautology.from(
      antisymm of (x := (x ⊓ topElem), y := x),
      s1,
      s2
    )
  }
}
