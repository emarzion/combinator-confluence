
Section star_rel.

Unset Implicit Arguments.

Variable X : Set.
Variable R : X -> X -> Prop.

Inductive star : X -> X -> Prop :=
  |star_refl : forall x, star x x
  |star_R    : forall x y z, star x y -> R y z -> star x z.

Lemma R_to_star : forall x y, R x y -> star x y.
Proof.
  intros.
  apply (star_R _ x _).
  apply star_refl.
  exact H.
Qed.

Lemma star_trans : forall x y z, star x y -> star y z -> star x z.
Proof.
  intros.
  induction H0.
  exact H.
  apply (star_R _ y _).
  apply IHstar.
  exact H.
  exact H1.
Qed.

End star_rel.

Set Implicit Arguments.

Section commuting_rels.

Variable X : Set.

Definition commute (R S : X -> X -> Prop) :=
  forall x y z, R x y -> S x z -> exists w, S y w /\ R z w.

Definition diamond(R : X -> X -> Prop) :=
 commute R R.

Definition confluent(R : X -> X -> Prop) :=
  diamond (star X R).

Definition subrel(R S : X -> X -> Prop) := forall x y, R x y -> S x y.

End commuting_rels.

Section diamond_confluence.

Variable X : Set.
Variables R S : X -> X -> Prop.

Variable subRS : subrel R S.
Variable subSRst : subrel S (star X R).
Variable dS : diamond S.

Lemma diamond_strip : commute S (star X R).
Proof.
  intros x y z Hxy Hxz.
  induction Hxz.
  exists y.
  split.
  apply star_refl.
  exact Hxy.
  destruct (IHHxz Hxy) as [w [Hw1 Hw2]].
  destruct (dS Hw2 (subRS H)) as [u [Hu1 Hu2]].
  exists u.
  split.
  apply (star_trans X _ _ w _).
  exact Hw1.
  apply subSRst.
  exact Hu1.
  exact Hu2.
Qed.

Lemma diamond_confluence : confluent R.
Proof.
  intros x y z Hxy Hxz.
  induction Hxy.
  exists z.
  split.
  exact Hxz.
  apply star_refl.
  destruct (IHHxy Hxz) as [w [Hw1 Hw2]].
  destruct (diamond_strip (subRS H) Hw1) as [u [Hu1 Hu2]].
  exists u.
  split.
  exact Hu1.
  apply (star_trans X _ _ w _).
  exact Hw2.
  apply subSRst.
  exact Hu2.
Qed.

End diamond_confluence.

