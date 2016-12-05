
Require Import Rels.

Set Implicit Arguments.

Inductive Term :=
  |S   : Term
  |K   : Term
  |App : Term -> Term -> Term.

Infix "#" := App (left associativity, at level 51).

Inductive red : Term -> Term -> Prop :=
  |S_red : forall x y z, red (S # x # y # z) (x # z # (y # z))
  |K_red : forall x y, red (K # x # y) x
  |App_l_red : forall x y z, red x y -> red (x # z) (y # z)
  |App_r_red : forall x y z, red x y -> red (z # x) (z # y).

Definition reds := star Term red.

Definition red_reds := R_to_star Term red.

Definition reds_trans := star_trans Term red.

Lemma App_l_reds : forall x y z, reds x y -> reds (x # z) (y # z).
Proof.
  intros.
  induction H.
  apply star_refl.
  apply (star_R _ _ _ (y # z) _).
  exact IHstar.
  apply App_l_red.
  exact H0.
Qed.

Lemma App_r_reds : forall x y z, reds x y -> reds (z # x) (z # y).
Proof.
  intros.
  induction H.
  apply star_refl.
  apply (star_R _ _ _ (z # y) _).
  exact IHstar.
  apply App_r_red.
  exact H0.
Qed.

Lemma App_reds : forall x1 x2 y1 y2, reds x1 y1 -> reds x2 y2 -> reds (x1 # x2) (y1 # y2).
Proof.
  intros.
  apply (reds_trans (App_l_reds _ H) (App_r_reds _ H0)).
Qed.

Lemma S_reds : forall x x' y y' z z', reds x x' -> reds y y' -> reds z z' ->
  reds (S # x # y # z) (x' # z' # (y' # z')).
Proof.
  intros.
  apply (star_R _ _ _ (S # x' # y' # z')).
  apply App_reds.
  apply App_reds.
  apply App_r_reds.
  exact H.
  exact H0.
  exact H1.
  apply S_red.
Qed.

Lemma K_reds : forall x x' y, reds x x' -> reds (K # x # y) x'.
Proof.
  intros.
  apply (star_R _ _ _ (K # x' # y)).
  apply App_l_reds.
  apply App_r_reds.
  exact H.
  apply K_red.
Qed.

Inductive pared : Term -> Term -> Prop :=
  |S_pared    : pared S S
  |K_pared    : pared K K
  |App_pared  : forall x x' y y', pared x x' -> pared y y' -> pared (x # y) (x' # y')
  |SApp_pared : forall x x' y y' z z', pared x x' -> pared y y' -> pared z z' ->
                  pared (S # x # y # z) (x' # z' # (y' # z'))
  |KApp_pared : forall x x' y, pared x x' -> pared (K # x # y) x'.

Lemma pared_refl : forall x, pared x x.
Proof.
  induction x.
  apply S_pared.
  apply K_pared.
  apply App_pared.
  exact IHx1.
  exact IHx2.
Qed.

Lemma red_pared : subrel red pared.
Proof.
  intros x y H.
  induction H.
  apply SApp_pared; apply pared_refl.
  apply KApp_pared; apply pared_refl.
  apply App_pared.
  exact IHred.
  apply pared_refl.
  apply App_pared.
  apply pared_refl.
  exact IHred.
Qed.

Lemma pared_reds : subrel pared reds.
Proof.
  intros x y H.
  induction H.
  apply star_refl.
  apply star_refl.
  apply App_reds.
  exact IHpared1.
  exact IHpared2.
  apply S_reds.
  exact IHpared1.
  exact IHpared2.
  exact IHpared3.
  apply K_reds.
  exact IHpared.
Qed.

Lemma pared_diamond : diamond pared.
Proof.
  intro x.
  induction x; intros y z H1 H2.
  exists S; split.
  inversion H1.
  apply S_pared.
  inversion H2.
  apply S_pared.
  exists K; split.
  inversion H1.
  apply K_pared.
  inversion H2.
  apply K_pared.
  inversion H1.
  inversion H2.
  destruct (IHx1 _ _ H3 H8) as [u [Hu1 Hu2]].
  destruct (IHx2 _ _ H5 H10) as [v [Hv1 Hv2]].
  exists (u # v); split; apply App_pared.
  exact Hu1.
  exact Hv1.
  exact Hu2.
  exact Hv2.
  destruct (IHx2 _ _ H5 H11) as [v [Hv1 Hv2]].
  rewrite <- H6 in H3.
  inversion H3.
  inversion H14.
  inversion H19.
  rewrite H6 in H3.
  rewrite <- H23 in H20.
  rewrite <- H20 in H15.
  rewrite <- H15 in H3.
  assert (pared x1 (S # x'0 # y'0)).
  rewrite <- H6.
  apply App_pared.
  apply App_pared.
  apply S_pared.
  exact H8.
  exact H9.
  destruct (IHx1 _ _ H3 H22) as [u [Hu1 Hu2]].
  inversion Hu1.
  inversion H26.
  inversion H31.
  exists (y'4 # v # (y'3 # v)); split.
  apply SApp_pared.
  exact H33.
  exact H28.
  exact Hv1.
  rewrite <- H27 in Hu2.
  rewrite <- H32 in Hu2.
  inversion Hu2.
  apply App_pared.
  apply App_pared.
  inversion H38.
  exact H46.
  exact Hv2.
  apply App_pared.
  exact H40.
  exact Hv2.
  rewrite <- H6 in H3.
  inversion H3.
  inversion H12.
  rewrite <- H6 in H2.
  inversion H2.
  inversion H18.
  inversion H23.
  assert (pared (K # x0) (K # y'0)).
  apply App_pared.
  apply K_pared.
  exact H14.
  assert (pared (K # x0) (K # y'2)).
  apply App_pared.
  apply K_pared.
  exact H25.
  rewrite H6 in H26,H28.
  destruct (IHx1 _ _ H26 H28) as [u [Hu1 Hu2]].
  inversion Hu1.
  inversion H31.
  exists y'3; split; apply KApp_pared.
  exact H33.
  rewrite <- H32 in Hu2.
  inversion Hu2.
  exact H40.
  assert (pared x1 (K # y'0)).
  rewrite <- H6.
  apply App_pared.
  exact K_pared.
  exact H14.
  assert (pared x1 (K # z)).
  rewrite <- H6.
  apply App_pared.
  exact K_pared.
  exact H19.
  destruct (IHx1 _ _ H20 H21) as [u [Hu1 Hu2]].
  inversion Hu1.
  exists y'1; split.
  apply KApp_pared.
  exact H26.
  rewrite <- H25 in Hu2.
  inversion Hu2.
  exact H32.
  rewrite <- H in H2.
  inversion H2.
  inversion H9.
  inversion H14.
  inversion H19.
  assert (pared x1 (S # x' # y')).
  rewrite <- H.
  apply App_pared.
  apply App_pared.
  exact S_pared.
  exact H3.
  exact H4.
  rewrite <- H20 in H15.
  rewrite <- H15 in H9.
  rewrite H in H9.
  destruct (IHx1 _ _ H9 H22) as [u [Hu1 Hu2]].
  inversion Hu2.
  inversion H26.
  destruct (IHx2 _ _ H6 H11) as [v [Hv1 Hv2]].
  exists (y'4 # v # (y'3 # v)); split.
  apply App_pared; apply App_pared.
  exact H33.
  exact Hv1.
  exact H28.
  exact Hv1.
  apply SApp_pared.
  rewrite <- H32 in H27.
  rewrite <- H27 in Hu1.
  inversion H19.
  rewrite <- H35 in Hu1.
  inversion Hu1.
  inversion H38.
  exact H46.
  rewrite <- H27 in Hu1.
  inversion H19.
  rewrite <- H35 in Hu1.
  inversion Hu1.
  exact H40.
  exact Hv2.
  assert (pared x1 (S # x' # y')).
  rewrite <- H.
  apply App_pared.
  apply App_pared.
  exact S_pared.
  exact H3.
  exact H4.
  assert (pared x1 (S # x'0 # y'0)).
  rewrite <- H.
  apply App_pared.
  apply App_pared.
  exact S_pared.
  exact H10.
  exact H12.
  destruct (IHx1 _ _ H14 H15) as [u [Hu1 Hu2]].
  inversion Hu1.
  inversion H18.
  inversion H23.
  destruct (IHx2 _ _ H6 H13) as [v [Hv1 Hv2]].
  exists (y'2 # v # (y'1 # v)).
  split.
  apply App_pared; apply App_pared.
  exact H25.
  exact Hv1.
  exact H20.
  exact Hv1.
  rewrite <- H27 in H24.
  rewrite <- H24 in H19.
  rewrite <- H19 in Hu2.
  inversion Hu2.
  inversion H30.
  apply App_pared; apply App_pared.
  exact H38.
  exact Hv2.
  exact H32.
  exact Hv2.
  rewrite <- H in H2.
  inversion H2.
  inversion H7.
  inversion H12.
  assert (pared x1 (K # y)).
  rewrite <- H.
  apply App_pared.
  apply K_pared.
  exact H4.
  assert (pared x1 (K # y'0)).
  rewrite <- H.
  apply App_pared.
  apply K_pared.
  exact H14.
  destruct (IHx1 _ _ H15 H17) as [u [Hu1 Hu2]].
  inversion Hu1.
  exists y'1.
  split.
  exact H22.
  apply KApp_pared.
  rewrite <- H21 in Hu2.
  inversion H20.
  rewrite <- H24 in Hu2.
  inversion Hu2.
  exact H29.
  assert (pared x1 (K # y)).
  rewrite <- H.
  apply App_pared.
  exact K_pared.
  exact H4.
  assert (pared x1 (K # z)).
  rewrite <- H.
  apply App_pared.
  exact K_pared.
  exact H8.
  destruct (IHx1 _ _ H9 H10) as [u [Hu1 Hu2]].
  inversion Hu1.
  exists y'.
  split.
  exact H15.
  rewrite <- H14 in Hu2.
  inversion H13.
  rewrite <- H17 in Hu2.
  inversion Hu2.
  exact H22.
Qed.

Lemma red_confluent : confluent red.
Proof.
  apply (diamond_confluence red_pared pared_reds pared_diamond).
Qed.

