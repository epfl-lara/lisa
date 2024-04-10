Inductive nat : Set :=
  | zero : nat
  | succ : nat -> nat
.

Theorem inhabited : exists _ : nat, True.
exists zero.
tauto.

Check(nat_ind).

Theorem neq_succ: forall n: nat, n <> succ n.
intro.
induction n.
discriminate.
injection.
apply IHn.

Inductive adt: Set :=
  | a : adt -> adt -> nat -> adt
  | b : adt -> nat -> adt
  | c : nat -> adt.

Theorem dab : forall (d : adt) (P : adt -> Set), P d.
intros.
induction d.
