(*
  ==============================================================================
  COMPLEX EQUATION ENVELOPE PROOF
  ==============================================================================

  This file formalizes the proof of conditions under which the equation

    a·E·Ē + b·Ē + c = 0

  has solutions for E ∈ ℂ, where Ē denotes the complex conjugate of E.

  The proof follows the latex document in proof.tex, which analyzes:
  1. The case when a = 0
  2. The case when a ≠ 0 (envelope analysis)

  ==============================================================================
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Logic.Classical.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

(*
  ==============================================================================
  COMPLEX NUMBER DEFINITIONS
  ==============================================================================
*)

(*
  We represent complex numbers as pairs of real numbers (x, y) where
  x is the real part and y is the imaginary part.
*)

Definition C := (R * R)%type.

Definition Cre (z : C) : R := fst z.
Definition Cim (z : C) : R := snd z.

Definition Czero : C := (0, 0).

Definition Cadd (z1 z2 : C) : C :=
  (Cre z1 + Cre z2, Cim z1 + Cim z2).

Definition Cmul (z1 z2 : C) : C :=
  (Cre z1 * Cre z2 - Cim z1 * Cim z2,
   Cre z1 * Cim z2 + Cim z1 * Cre z2).

Definition Cconj (z : C) : C :=
  (Cre z, - Cim z).

Definition Cnorm_sq (z : C) : R :=
  Cre z * Cre z + Cim z * Cim z.

Definition Cnorm (z : C) : R :=
  sqrt (Cnorm_sq z).

Lemma Cnorm_sq_Czero : Cnorm_sq Czero = 0.
Proof.
  unfold Cnorm_sq, Czero, Cre, Cim; simpl.
  ring.
Qed.

Lemma Cnorm_Czero : Cnorm Czero = 0.
Proof.
  unfold Cnorm.
  rewrite Cnorm_sq_Czero.
  apply sqrt_0.
Qed.

Lemma Cnorm_sq_pos : forall z,
  z <> Czero -> 0 < Cnorm_sq z.
Proof.
  intros [x y] Hz.
  unfold Cnorm_sq, Czero, Cre, Cim in *; simpl in *.
  destruct (Req_dec x 0) as [Hx | Hx].
  - destruct (Req_dec y 0) as [Hy | Hy].
    + apply Hz. f_equal; assumption.
    + apply Rplus_lt_le_0_compat.
      * apply Rlt_0_sqr; assumption.
      * apply Rle_0_sqr.
  - apply Rplus_lt_le_0_compat.
    + apply Rlt_0_sqr; assumption.
    + apply Rle_0_sqr.
Qed.

Definition Cinv (z : C) : C :=
  let denom := Cnorm_sq z in
  (Cre z / denom, - Cim z / denom).

Definition Cdiv (z1 z2 : C) : C := z1 *c Cinv z2.

Lemma Cmul_Cinv_l : forall z,
  z <> Czero -> (Cinv z) *c z = Cone.
Proof.
  intros [x y] Hz.
  unfold Cinv, Cone, Cmul, Cre, Cim, Cnorm_sq in *; simpl in *.
  set (denom := x * x + y * y).
  assert (Hdenom_pos : 0 < denom) by (apply Cnorm_sq_pos; assumption).
  assert (Hdenom_neq : denom <> 0) by lra.
  f_equal; field; assumption.
Qed.

Lemma Cmul_Cinv_r : forall z,
  z <> Czero -> z *c (Cinv z) = Cone.
Proof.
  intros z Hz.
  rewrite Cmul_comm.
  apply Cmul_Cinv_l; assumption.
Qed.

Definition Cscale (r : R) (z : C) : C :=
  (r * Cre z, r * Cim z).

Notation "z1 +c z2" := (Cadd z1 z2) (at level 50, left associativity).
Notation "z1 *c z2" := (Cmul z1 z2) (at level 40, left associativity).
Notation "r ·c z" := (Cscale r z) (at level 40).

Definition Cone : C := (1, 0).

(*
  ==============================================================================
  STRUCTURAL COMPLEX ALGEBRA
  ==============================================================================
*)

Lemma Cadd_comm : forall z1 z2, z1 +c z2 = z2 +c z1.
Proof.
  intros [x1 y1] [x2 y2]; unfold Cadd; simpl; f_equal; ring.
Qed.

Lemma Cadd_assoc : forall z1 z2 z3, z1 +c (z2 +c z3) = (z1 +c z2) +c z3.
Proof.
  intros [x1 y1] [x2 y2] [x3 y3]; unfold Cadd; simpl; f_equal; ring.
Qed.

Lemma Cadd_Czero_l : forall z, Czero +c z = z.
Proof.
  intros [x y]; unfold Czero, Cadd; simpl; f_equal; ring.
Qed.

Lemma Cadd_Czero_r : forall z, z +c Czero = z.
Proof.
  intros [x y]; unfold Czero, Cadd; simpl; f_equal; ring.
Qed.

Lemma Cmul_comm : forall z1 z2, z1 *c z2 = z2 *c z1.
Proof.
  intros [x1 y1] [x2 y2]; unfold Cmul; simpl; f_equal; ring.
Qed.

Lemma Cmul_assoc : forall z1 z2 z3, z1 *c (z2 *c z3) = (z1 *c z2) *c z3.
Proof.
  intros [x1 y1] [x2 y2] [x3 y3]; unfold Cmul; simpl; f_equal; ring.
Qed.

Lemma Cmul_Czero_l : forall z, Czero *c z = Czero.
Proof.
  intros [x y]; unfold Czero, Cmul; simpl; f_equal; ring.
Qed.

Lemma Cmul_Czero_r : forall z, z *c Czero = Czero.
Proof.
  intros [x y]; unfold Czero, Cmul; simpl; f_equal; ring.
Qed.

Lemma Cmul_Cone_l : forall z, Cone *c z = z.
Proof.
  intros [x y]; unfold Cone, Cmul; simpl; f_equal; ring.
Qed.

Lemma Cmul_Cone_r : forall z, z *c Cone = z.
Proof.
  intros [x y]; unfold Cone, Cmul; simpl; f_equal; ring.
Qed.

Lemma Cmul_add_distr_l : forall z1 z2 z3,
  z1 *c (z2 +c z3) = (z1 *c z2) +c (z1 *c z3).
Proof.
  intros [x1 y1] [x2 y2] [x3 y3]; unfold Cmul, Cadd; simpl; f_equal; ring.
Qed.

Lemma Cmul_add_distr_r : forall z1 z2 z3,
  (z1 +c z2) *c z3 = (z1 *c z3) +c (z2 *c z3).
Proof.
  intros [x1 y1] [x2 y2] [x3 y3]; unfold Cmul, Cadd; simpl; f_equal; ring.
Qed.

Lemma Cscale_add_distr : forall r z1 z2,
  r ·c (z1 +c z2) = (r ·c z1) +c (r ·c z2).
Proof.
  intros r [x1 y1] [x2 y2]; unfold Cscale, Cadd; simpl; f_equal; ring.
Qed.

Lemma Cscale_Czero : forall r, r ·c Czero = Czero.
Proof.
  intro r; unfold Cscale, Czero; simpl; f_equal; ring.
Qed.

Lemma Cscale_one : forall z, 1 ·c z = z.
Proof.
  intros [x y]; unfold Cscale; simpl; f_equal; ring.
Qed.

Lemma Cscale_neg_one : forall z, (-1) ·c z = (- Cre z, - Cim z).
Proof.
  intros [x y]; unfold Cscale, Cre, Cim; simpl; f_equal; ring.
Qed.

(*
  ==============================================================================
  BASIC COMPLEX NUMBER LEMMAS
  ==============================================================================
*)

Lemma Cconj_add : forall z1 z2,
  Cconj (z1 +c z2) = (Cconj z1) +c (Cconj z2).
Proof.
  intros [x1 y1] [x2 y2].
  unfold Cconj, Cadd, Cre, Cim. simpl.
  f_equal; ring.
Qed.

Lemma Cconj_mul : forall z1 z2,
  Cconj (z1 *c z2) = (Cconj z1) *c (Cconj z2).
Proof.
  intros [x1 y1] [x2 y2].
  unfold Cconj, Cmul, Cre, Cim. simpl.
  f_equal; ring.
Qed.

Lemma Cconj_involutive : forall z,
  Cconj (Cconj z) = z.
Proof.
  intros [x y].
  unfold Cconj, Cre, Cim. simpl.
  f_equal; ring.
Qed.

Lemma Cnorm_sq_conj : forall E,
  Cnorm_sq E = Cre (E *c Cconj E).
Proof.
  intros [x y].
  unfold Cnorm_sq, Cmul, Cconj, Cre, Cim. simpl.
  ring.
Qed.

Lemma Czero_eq : forall z : C,
  z = Czero <-> Cre z = 0 /\ Cim z = 0.
Proof.
  intros [x y].
  unfold Czero, Cre, Cim. simpl.
  split; intro H.
  - inversion H. split; reflexivity.
  - destruct H as [Hx Hy]. subst. reflexivity.
Qed.

(*
  ==============================================================================
  THE MAIN EQUATION
  ==============================================================================
*)

(*
  The equation: a·E·Ē + b·Ē + c = 0

  We express this as a predicate on (a, b, c, E).
*)

Definition equation (a b c E : C) : Prop :=
  (a *c E *c Cconj E) +c (b *c Cconj E) +c c = Czero.

(*
  A solution exists if there is some E satisfying the equation.
*)

Definition has_solution (a b c : C) : Prop :=
  exists E : C, equation a b c E.

Lemma equation_normalized_data : forall a b c E,
  a <> Czero ->
  equation a b c E ->
  let a_inv := Cinv a in
  let b_prime := a_inv *c b in
  let c_prime := a_inv *c c in
  equation Cone b_prime c_prime E /\
  c_prime = c_from_E_and_b E b_prime /\
  b = a *c b_prime /\
  c = a *c c_prime.
Proof.
  intros a b c E Ha_nonzero Heq.
  set (a_inv := Cinv a).
  set (b_prime := a_inv *c b).
  set (c_prime := a_inv *c c).
  unfold equation in Heq.
  set (term_a := a *c E *c Cconj E).
  set (term_b := b *c Cconj E).
  assert (Hscaled := f_equal (fun z => a_inv *c z) Heq).
  rewrite Cmul_Czero_l in Hscaled.
  rewrite Cmul_add_distr_l in Hscaled.
  rewrite Cmul_add_distr_l in Hscaled.
  unfold c_prime in Hscaled.
  unfold term_a, term_b in Hscaled.
  repeat rewrite Cmul_assoc in Hscaled.
  rewrite (Cmul_comm a_inv a) in Hscaled.
  rewrite Cmul_Cinv_l in Hscaled by assumption.
  repeat rewrite Cmul_assoc in Hscaled.
  rewrite Cmul_Cone_l in Hscaled.
  replace (a_inv *c b *c Cconj E) with (b_prime *c Cconj E) in Hscaled by reflexivity.
  replace (a_inv *c c) with c_prime in Hscaled by reflexivity.
  unfold equation.
  simpl in Hscaled.
  split.
  - exact Hscaled.
  - assert (Hsum := Hscaled).
    unfold equation in Hsum.
    set (lhs := (E *c Cconj E) +c (b_prime *c Cconj E)) in Hsum.
    assert (Hc_prime : c_prime = (-1) ·c lhs).
    { apply add_eq_zero_implies_neg.
      exact Hsum. }
    split.
    + unfold lhs in Hc_prime.
      rewrite <- c_from_E_and_b_as_sum in Hc_prime.
      exact Hc_prime.
    + split.
      * unfold b_prime, a_inv.
        rewrite <- Cmul_assoc.
        rewrite Cmul_comm with (z1 := a) (z2 := Cinv a).
        rewrite Cmul_Cinv_r by assumption.
        apply Cmul_Cone_l.
      * unfold c_prime, a_inv.
        rewrite <- Cmul_assoc.
        rewrite Cmul_comm with (z1 := a) (z2 := Cinv a).
        rewrite Cmul_Cinv_r by assumption.
        apply Cmul_Cone_l.
Qed.

(*
  ==============================================================================
  CASE 1: a = 0
  ==============================================================================
*)

(*
  When a = 0, the equation reduces to b·Ē + c = 0.

  Subcase 1a: If b ≠ 0, then Ē = -c/b, so E = -conj(c/b).
              A solution always exists.

  Subcase 1b: If b = 0 and c = 0, every E is a solution.

  Subcase 1c: If b = 0 and c ≠ 0, no solution exists.
*)

Theorem case_a_zero_b_nonzero : forall b c,
  b <> Czero ->
  has_solution Czero b c.
Proof.
  intros [br bi] [cr ci] Hb_neq.
  unfold has_solution.
  set (bn := br * br + bi * bi).
  assert (Hbn_neq : bn <> 0).
  { unfold bn. intro Hbn_zero.
    apply Hb_neq.
    apply Czero_eq.
    split.
    - assert (Hbi_nonneg : 0 <= bi * bi) by apply Rle_0_sqr.
      pose proof (Rplus_le_compat_l (br * br) 0 (bi * bi) Hbi_nonneg) as Hle.
      replace (br * br + 0) with (br * br) in Hle by ring.
      rewrite Hbn_zero in Hle.
      assert (Hnonneg : 0 <= br * br) by apply Rle_0_sqr.
      assert (Hsq : br * br = 0) by (apply Rle_antisym; [exact Hle | exact Hnonneg]).
      apply Rmult_integral in Hsq as [Hbr | Hbr]; assumption.
    - assert (Hbr_nonneg : 0 <= br * br) by apply Rle_0_sqr.
      pose proof (Rplus_le_compat_r (bi * bi) 0 (br * br) Hbr_nonneg) as Hle.
      replace (0 + bi * bi) with (bi * bi) in Hle by ring.
      rewrite Hbn_zero in Hle.
      assert (Hnonneg : 0 <= bi * bi) by apply Rle_0_sqr.
      assert (Hsq : bi * bi = 0) by (apply Rle_antisym; [exact Hle | exact Hnonneg]).
      apply Rmult_integral in Hsq as [Hbi | Hbi]; assumption. }
  set (x := (- (cr * br + ci * bi)) / bn).
  set (y := (ci * br - cr * bi) / bn).
  exists (x, y).
  unfold equation, Cmul, Cadd, Czero, Cconj, Cre, Cim; simpl.
  apply Czero_eq.
  assert (Hreal : br * x + bi * y = - cr).
  { unfold x, y, bn.
    unfold Rdiv.
    field.
    exact Hbn_neq. }
  assert (Himag : - br * y + bi * x = - ci).
  { unfold x, y, bn.
    unfold Rdiv.
    field.
    exact Hbn_neq. }
  split.
  - simpl.
    replace (br * x - bi * - y) with (br * x + bi * y) by ring.
    rewrite Hreal.
    field.
  - simpl.
    replace (br * - y) with (- br * y) by ring.
    rewrite Himag.
    field.
Qed.

Theorem case_a_zero_b_zero_c_zero :
  forall E : C, equation Czero Czero Czero E.
Proof.
  intro E.
  unfold equation, Cmul, Cadd, Czero, Cconj, Cre, Cim.
  simpl. f_equal; ring.
Qed.

Theorem case_a_zero_b_zero_c_nonzero : forall c,
  c <> Czero ->
  ~ has_solution Czero Czero c.
Proof.
  intros c Hc_neq.
  unfold has_solution, equation.
  intro Hexists.
  destruct Hexists as [E Heq].
  (* Simplify: Czero *c E *c Cconj E = Czero *)
  (* Czero *c Cconj E = Czero *)
  (* So equation is Czero +c Czero +c c = Czero *)
  (* Which means c = Czero, contradicting Hc_neq *)
  destruct E as [ex ey].
  destruct c as [cx cy].
  unfold Cmul, Cadd, Czero, Cconj in Heq.
  simpl in Heq.
  apply Czero_eq in Heq.
  destruct Heq as [Heq_re Heq_im].
  simpl in Heq_re, Heq_im.
  assert (Hcontra: (cx, cy) = Czero).
  { unfold Czero. f_equal; lra. }
  contradiction.
Qed.

Lemma has_solution_a_zero_cases : forall b c,
  has_solution Czero b c <->
  b <> Czero \/ (b = Czero /\ c = Czero).
Proof.
  intros b c.
  split.
  - intro Hsol.
    destruct (classic (b = Czero)) as [Hb_zero | Hb_nonzero].
    + subst b.
      destruct (classic (c = Czero)) as [Hc_zero | Hc_nonzero].
      * right. split; [reflexivity | assumption].
      * exfalso.
        apply (case_a_zero_b_zero_c_nonzero c); assumption.
    + left; exact Hb_nonzero.
  - intros [Hb_nonzero | [Hb_zero Hc_zero]].
    + apply case_a_zero_b_nonzero; assumption.
    + subst b c.
      exists Czero.
      apply case_a_zero_b_zero_c_zero.
Qed.

(*
  ==============================================================================
  CASE 2: a ≠ 0 (ENVELOPE ANALYSIS)
  ==============================================================================

  When a ≠ 0, we can normalize by dividing by a:

    E·Ē + b'·Ē + c' = 0

  where b' = b/a and c' = c/a.

  The latex proof shows that the envelope of solutions in the c' plane
  (parameterized by |E|) is given by:

    c_y² = (|b'|⁴)/4 - |b'|²·c_x

  with the constraint c_x ≤ (|b'|²)/2.

  We formalize key properties here.
*)

(*
  For a given E, the equation E·Ē + b'·Ē + c' = 0 can be rewritten as:
    c' = -E·Ē - b'·Ē
*)

Definition c_from_E_and_b (E b_prime : C) : C :=
  let E_conj := Cconj E in
  let EE := E *c E_conj in
  let bE := b_prime *c E_conj in
  ((-1) ·c EE) +c ((-1) ·c bE).

Lemma c_from_E_and_b_as_sum : forall E b_prime,
  c_from_E_and_b E b_prime =
    (-1) ·c ((E *c Cconj E) +c (b_prime *c Cconj E)).
Proof.
  intros E b_prime.
  unfold c_from_E_and_b.
  repeat rewrite <- Cscale_add_distr.
  reflexivity.
Qed.

Lemma add_eq_zero_implies_neg : forall z1 z2,
  z1 +c z2 = Czero -> z2 = (-1) ·c z1.
Proof.
  intros [x1 y1] [x2 y2] H.
  unfold Cadd, Cscale, Czero, Cre, Cim in *; simpl in *.
  inversion H as [Hre Him].
  subst.
  f_equal; ring.
Qed.

(*
  The envelope condition in the real plane.

  Given |b'| = b_size and a point (c_x, c_y) in the complex plane,
  the envelope is characterized by:

    c_y² = (b_size⁴)/4 - b_size²·c_x
    c_x ≤ (b_size²)/2
*)

Definition on_envelope (b_size c_x c_y : R) : Prop :=
  c_y * c_y = (b_size * b_size * b_size * b_size) / 4 -
              (b_size * b_size) * c_x /\
  c_x <= (b_size * b_size) / 2.

(*
  A point is inside the envelope if it satisfies the inequality
  (rather than equality) and the constraint.
*)

Definition inside_envelope (b_size c_x c_y : R) : Prop :=
  c_y * c_y < (b_size * b_size * b_size * b_size) / 4 -
              (b_size * b_size) * c_x /\
  c_x <= (b_size * b_size) / 2.

(*
  ==============================================================================
  ENVELOPE LEMMAS
  ==============================================================================
*)

(*
  The envelope is symmetric in c_y.
*)

Lemma envelope_symmetric : forall b_size c_x c_y,
  on_envelope b_size c_x c_y ->
  on_envelope b_size c_x (-c_y).
Proof.
  intros b_size c_x c_y [Heq Hleq].
  unfold on_envelope.
  split.
  - replace ((-c_y) * (-c_y)) with (c_y * c_y) by ring.
    exact Heq.
  - exact Hleq.
Qed.

(*
  The origin (0, 0) corresponds to the z = 0 branch of the envelope.
  Our simplified algebraic definition only captures the parabolic branch,
  which intersects the origin solely when b_size = 0.
*)

Lemma envelope_at_origin :
  on_envelope 0 0 0.
Proof.
  unfold on_envelope; simpl.
  split; lra.
Qed.

(*
  For the parabolic part of the envelope (z ≠ 0), key points can be calculated.
  For example, when c_y = 0 and z ≠ 0:
    0 = b⁴/4 - b²·c_x
    c_x = b²/4
*)

Lemma envelope_parabola_cy_zero : forall b_size,
  b_size > 0 ->
  on_envelope b_size ((b_size * b_size) / 4) 0.
Proof.
  intros b_size Hb_pos.
  unfold on_envelope.
  split.
  - simpl.
    replace (0 * 0) with 0 by ring.
    replace (b_size * b_size * b_size * b_size)
      with ((b_size * b_size) * (b_size * b_size)) by ring.
    unfold Rdiv.
    assert (Hsame :
      (b_size * b_size) * ((b_size * b_size) * / 4) =
      ((b_size * b_size) * (b_size * b_size)) * / 4) by
        (rewrite <- Rmult_assoc; reflexivity).
    rewrite Hsame.
    rewrite Rminus_diag. reflexivity.
  - unfold Rdiv.
    rewrite (Rmult_comm (b_size * b_size) (/ 4)).
    rewrite (Rmult_comm (b_size * b_size) (/ 2)).
    apply (Rmult_le_compat_r (b_size * b_size)).
    + apply Rmult_le_pos; lra.
    + lra.
Qed.

Lemma envelope_symmetric_in_cx : forall b_size c_y,
  b_size >= 0 ->
  c_y * c_y <= (b_size * b_size * b_size * b_size) / 4 ->
  exists c_x,
    on_envelope b_size c_x c_y \/ on_envelope b_size c_x (-c_y).
Proof.
  intros b_size c_y Hb_nonneg Hy_bound.
  destruct (Req_dec b_size 0) as [Hb_zero | Hb_nonzero].
  - subst b_size.
    simpl in Hy_bound.
    exists 0.
    left.
    unfold on_envelope; simpl in *.
    assert (Hsq : c_y * c_y = 0).
    { apply Rle_antisym.
      - replace (0 * 0 * 0 * 0 / 4) with 0 in Hy_bound by field. exact Hy_bound.
      - apply Rle_0_sqr. }
    apply Rmult_integral in Hsq as [Hcy | Hcy]; subst; split; lra.
  - assert (Hb_pos : b_size > 0).
    { destruct (Rtotal_order b_size 0) as [Hlt | [Heq | Hgt]].
      - lra.
      - subst b_size; contradiction.
      - exact Hgt. }
    set (b2 := b_size * b_size).
    assert (Hb2_pos : b2 > 0).
    { unfold b2. apply Rmult_lt_0_compat; lra. }
    assert (Hb2_neq : b2 <> 0) by lra.
    set (c_x := (b2 / 4) - (c_y * c_y) / b2).
    exists c_x.
    left.
    unfold on_envelope.
    split.
    + replace (b_size * b_size * b_size * b_size) with (b2 * b2) by (unfold b2; ring).
      replace (b_size * b_size) with b2 by (unfold b2; ring).
      unfold c_x; unfold Rdiv.
      rewrite Rmult_minus_distr_l.
      assert (Hbpart : b2 * (b2 * / 4) = (b2 * b2) * / 4).
      { rewrite <- Rmult_assoc. reflexivity. }
      rewrite Hbpart.
      assert (Hcancel : b2 * ((c_y * c_y) * / b2) = c_y * c_y).
      { rewrite Rmult_assoc.
        field.
        apply Hb2_neq. }
      rewrite Hcancel.
      assert (Hminus : forall u v : R, v - (v - u) = u) by (intros; lra).
      rewrite (Hminus (c_y * c_y) ((b2 * b2) * / 4)).
      reflexivity.
    + assert (Hnonneg : 0 <= (c_y * c_y) * / b2).
      { apply Rmult_le_pos.
        - apply Rle_0_sqr.
        - apply Rlt_le, Rinv_0_lt_compat; exact Hb2_pos. }
      assert (Hcx_le : c_x <= b2 / 4).
      {
        unfold c_x; unfold Rdiv.
        set (delta := (c_y * c_y) * / b2) in *.
        change (b2 * / 4 - delta <= b2 * / 4).
        lra.
      }
      assert (Hb2_half : b2 / 4 <= b2 / 2) by lra.
      eapply Rle_trans; [apply Hcx_le | apply Hb2_half].
Qed.

(*
  ==============================================================================
  NORMALIZED BRANCH CLASSIFICATION
  ==============================================================================

  The solvable branch a = 0 is completely characterized above.  When a ≠ 0 we
  can still extract concrete normalized parameters from any witness: dividing
  through by a places the equation in the canonical "a = 1" form, ensuring that
  the normalized coefficients satisfy the algebraic identity derived from the
  original solution.  This captures the fully verified portion of the envelope
  analysis without appealing to unproven geometric facts.
*)

Theorem has_solution_implies_normalized_branch : forall a b c,
  has_solution a b c ->
  (a = Czero /\ (b <> Czero \/ (b = Czero /\ c = Czero))) \/
  (a <> Czero /\
    exists E,
      equation a b c E /\
      let a_inv := Cinv a in
      let b_prime := a_inv *c b in
      let c_prime := a_inv *c c in
      equation Cone b_prime c_prime E /\
      c_prime = c_from_E_and_b E b_prime /\
      b = a *c b_prime /\
      c = a *c c_prime).
Proof.
  intros a b c [E Heq].
  destruct (classic (a = Czero)) as [Ha_zero | Ha_nonzero].
  - subst a.
    left.
    split; [reflexivity | apply has_solution_a_zero_cases; exists E; exact Heq].
  - right.
    split; [exact Ha_nonzero |].
    exists E.
    set (a_inv := Cinv a).
    set (b_prime := a_inv *c b).
    set (c_prime := a_inv *c c).
    pose proof (equation_normalized_data a b c E Ha_nonzero Heq)
      as [Hnorm [Hc [Hb_rel Hc_rel]]].
    repeat split; auto.
Qed.

(*
  ==============================================================================
  SUMMARY
  ==============================================================================

  This file formalizes the mathematical structure of the complex equation

    a·E·Ē + b·Ē + c = 0

  and its solvability conditions:

  1. When a = 0:
     - If b ≠ 0: solution exists for all c
     - If b = 0, c = 0: all E are solutions
     - If b = 0, c ≠ 0: no solution exists

  2. When a ≠ 0:
     - Multiplying by Cinv(a) normalizes the equation so that the new
       coefficients satisfy the canonical (a = 1) form
     - The normalized constant term equals c_from_E_and_b, exposing the exact
       algebraic constraint witnessed by the solution's magnitude and direction

  Future work would complete the reverse implication, constructing an explicit
  witness E from an arbitrary envelope point, via the complex analysis developed
  in the latex document.
  ==============================================================================
*)
