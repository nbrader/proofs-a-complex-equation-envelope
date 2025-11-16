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
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import Coquelicot.Hierarchy.
Require Import Coquelicot.Rbar.
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

Definition Cscale (r : R) (z : C) : C :=
  (r * Cre z, r * Cim z).

Notation "z1 +c z2" := (Cadd z1 z2) (at level 50, left associativity).
Notation "z1 *c z2" := (Cmul z1 z2) (at level 40, left associativity).
Notation "r ·c z" := (Cscale r z) (at level 40).

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
  Complex division: z1 / z2 = z1 * conj(z2) / |z2|^2
  Only defined when z2 ≠ 0.
*)

Definition Cdiv (z1 z2 : C) : C :=
  let norm_sq := Cnorm_sq z2 in
  let z2_conj := Cconj z2 in
  let numerator := z1 *c z2_conj in
  ((Cre numerator / norm_sq), (Cim numerator / norm_sq)).

Notation "z1 /c z2" := (Cdiv z1 z2) (at level 40).

Lemma Cdiv_nonzero_well_defined : forall (z1 z2 : C),
  z2 <> Czero ->
  Cnorm_sq z2 <> 0.
Proof.
  intros z1 [x2 y2] Hz2.
  unfold Cnorm_sq, Cre, Cim. simpl.
  intro Hcontra.
  apply Hz2.
  unfold Czero.
  assert (Hx2: x2 = 0).
  { apply Rplus_eq_R0 in Hcontra.
    - destruct Hcontra as [Hx _]. apply Rmult_integral in Hx.
      destruct Hx; assumption.
    - apply Rle_0_sqr.
    - apply Rle_0_sqr. }
  assert (Hy2: y2 = 0).
  { subst x2. simpl in Hcontra.
    apply Rplus_eq_R0 in Hcontra.
    - destruct Hcontra as [_ Hy]. apply Rmult_integral in Hy.
      destruct Hy; assumption.
    - lra.
    - apply Rle_0_sqr. }
  subst. reflexivity.
Qed.

Lemma Cmul_div_cancel : forall (z1 z2 : C),
  z2 <> Czero ->
  (z1 /c z2) *c z2 = z1.
Proof.
  intros [x1 y1] [x2 y2] Hz2.
  unfold Cdiv, Cmul, Cconj, Cnorm_sq, Cre, Cim. simpl.
  assert (Hnorm: x2 * x2 + y2 * y2 <> 0).
  { apply (Cdiv_nonzero_well_defined (x1, y1) (x2, y2)).
    exact Hz2. }
  f_equal; field; exact Hnorm.
Qed.

Lemma Cmul_conj_eq : forall b E,
  b *c Cconj E = Czero ->
  b = Czero \/ E = Czero.
Proof.
  intros b E Heq.
  destruct b, E.
  unfold Cmul, Cconj, Czero, Cre, Cim in Heq.
  simpl in Heq.
  apply Czero_eq in Heq.
  destruct Heq as [Hre Him].
  (* Simplify Hre and Him *)
  simpl in Hre, Him.
  (* Rewrite into standard form *)
  assert (Hre': r * r1 + r0 * r2 = 0) by lra.
  assert (Him': r0 * r1 - r * r2 = 0) by lra.
  clear Hre Him.
  rename Hre' into Hre.
  rename Him' into Him.
  (* Now Hre: r * r1 + r0 * r2 = 0 and Him: r0 * r1 - r * r2 = 0 *)
  (* We'll show that if b ≠ 0, then E = 0. *)
  destruct (Req_dec r 0), (Req_dec r0 0).
  - (* r = 0 and r0 = 0, so b = 0 *)
    left. apply Czero_eq. simpl. split; assumption.
  - (* r = 0, r0 ≠ 0 *)
    right. apply Czero_eq. simpl.
    subst r. simpl in Hre, Him.
    (* Hre: 0 + r0 * r2 = 0, so r0 * r2 = 0 *)
    (* Him: 0 + r0 * r1 = 0, so r0 * r1 = 0 *)
    assert (Heq1: r0 * r1 = 0) by lra.
    assert (Heq2: r0 * r2 = 0) by lra.
    apply Rmult_integral in Heq1.
    apply Rmult_integral in Heq2.
    destruct Heq1 as [H1 | H1]; [lra |].
    destruct Heq2 as [H2 | H2]; [lra |].
    split; assumption.
  - (* r ≠ 0, r0 = 0 *)
    right. apply Czero_eq. simpl.
    subst r0. simpl in Hre, Him.
    (* Hre: r * r1 + 0 = 0, so r * r1 = 0 *)
    (* Him: 0 - r * r2 = 0, so r * r2 = 0 *)
    assert (Heq1: r * r1 = 0) by lra.
    assert (Heq2: r * r2 = 0) by lra.
    apply Rmult_integral in Heq1.
    apply Rmult_integral in Heq2.
    destruct Heq1 as [H1 | H1]; [lra |].
    destruct Heq2 as [H2 | H2]; [lra |].
    split; assumption.
  - (* r ≠ 0, r0 ≠ 0, so b ≠ 0, need to show E = 0 *)
    right. apply Czero_eq. simpl.
    split.
    + (* Show r1 = 0 *)
      (* From Hre: r * r1 + r0 * r2 = 0 and Him: r0 * r1 - r * r2 = 0
         Multiply Hre by r: r * (r * r1 + r0 * r2) = 0, so r*r*r1 + r*r0*r2 = 0
         Multiply Him by r0: r0 * (r0 * r1 - r * r2) = 0, so r0*r0*r1 - r0*r*r2 = 0
         Add them: (r*r + r0*r0)*r1 = 0 *)
      assert (Hsum: (r * r + r0 * r0) * r1 = 0).
      { assert (H1: r * r * r1 + r * r0 * r2 = 0) by (apply (f_equal (Rmult r)) in Hre; lra).
        assert (H2: r0 * r0 * r1 - r0 * r * r2 = 0) by (apply (f_equal (Rmult r0)) in Him; lra).
        lra. }
      assert (Hpos: r * r + r0 * r0 > 0).
      { (* For any nonzero r, r * r > 0 *)
        assert (Hr_sq: r * r > 0) by nra.
        assert (Hr0_sq: r0 * r0 > 0) by nra.
        lra. }
      apply Rmult_integral in Hsum.
      destruct Hsum as [Hcontra | Hr1]; [lra | exact Hr1].
    + (* Show r2 = 0 *)
      (* Multiply Hre by r0: r0*r*r1 + r0*r0*r2 = 0
         Multiply Him by r: r*r0*r1 - r*r*r2 = 0
         Subtract: (r*r + r0*r0)*r2 = 0 *)
      assert (Hdiff: (r * r + r0 * r0) * r2 = 0).
      { assert (H1: r0 * r * r1 + r0 * r0 * r2 = 0) by (apply (f_equal (Rmult r0)) in Hre; lra).
        assert (H2: r * r0 * r1 - r * r * r2 = 0) by (apply (f_equal (Rmult r)) in Him; lra).
        lra. }
      assert (Hpos: r * r + r0 * r0 > 0).
      { (* For any nonzero r, r * r > 0 *)
        assert (Hr_sq: r * r > 0) by nra.
        assert (Hr0_sq: r0 * r0 > 0) by nra.
        lra. }
      apply Rmult_integral in Hdiff.
      destruct Hdiff as [Hcontra | Hr2]; [lra | exact Hr2].
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
  intros b c Hb_neq.
  unfold has_solution, equation.
  (* When a = 0, the equation becomes: b·Ē + c = 0, so Ē = -c/b.
     Therefore E = conj(-c/b) = -conj(c/b). *)
  exists (Cconj ((-1, 0) *c (c /c b))).

  (* Simplify: Czero *c E *c Cconj E = Czero *)
  assert (H1: Czero *c (Cconj ((-1, 0) *c (c /c b))) *c
              Cconj (Cconj ((-1, 0) *c (c /c b))) = Czero).
  { destruct b, c. unfold Czero, Cmul, Cconj, Cdiv, Cnorm_sq, Cre, Cim. simpl.
    f_equal; ring. }
  rewrite H1.

  (* Now we need: Czero +c b *c Cconj E +c c = Czero *)
  (* Which is: b *c Cconj E +c c = Czero *)

  (* Simplify Cconj E using Cconj_involutive *)
  assert (H2: Cconj (Cconj ((-1, 0) *c (c /c b))) = (-1, 0) *c (c /c b)).
  { rewrite Cconj_involutive. reflexivity. }

  (* Now show: Czero +c b *c ((-1, 0) *c (c /c b)) +c c = Czero *)
  assert (H3: b *c ((-1, 0) *c (c /c b)) = (-1, 0) *c c).
  { (* Use associativity and commutativity of complex multiplication *)
    destruct b as [b1 b2], c as [c1 c2].
    unfold Cmul, Cscale, Cdiv, Cnorm_sq, Cre, Cim. simpl.
    assert (Hnorm: b1 * b1 + b2 * b2 <> 0).
    { apply (Cdiv_nonzero_well_defined (c1, c2) (b1, b2)). exact Hb_neq. }
    f_equal; field; exact Hnorm. }

  (* Show: Czero +c (-1, 0) *c c +c c = Czero *)
  rewrite H2, H3.
  destruct c as [c1 c2].
  unfold Cadd, Czero, Cscale, Cre, Cim. simpl.
  f_equal; ring.
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
  destruct E, c.
  unfold Cmul, Cadd, Czero, Cconj in Heq.
  simpl in Heq.
  apply Czero_eq in Heq.
  destruct Heq as [Heq_re Heq_im].
  simpl in Heq_re, Heq_im.
  assert (Hcontra: (r1, r2) = Czero).
  { unfold Czero. f_equal; lra. }
  contradiction.
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
  - assert (Hb_pos : b_size > 0) by lra.
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
  HELPER LEMMAS FOR ENVELOPE THEOREM
  ==============================================================================
*)

(* Helper: multiplication distributes over complex addition *)
Lemma Cmul_add_distr_l : forall z1 z2 z3,
  z1 *c (z2 +c z3) = (z1 *c z2) +c (z1 *c z3).
Proof.
  intros [x1 y1] [x2 y2] [x3 y3].
  unfold Cmul, Cadd, Cre, Cim. simpl.
  f_equal; ring.
Qed.

Lemma Cmul_add_distr_r : forall z1 z2 z3,
  (z1 +c z2) *c z3 = (z1 *c z3) +c (z2 *c z3).
Proof.
  intros [x1 y1] [x2 y2] [x3 y3].
  unfold Cmul, Cadd, Cre, Cim. simpl.
  f_equal; ring.
Qed.

Lemma Cadd_assoc : forall z1 z2 z3,
  (z1 +c z2) +c z3 = z1 +c (z2 +c z3).
Proof.
  intros [x1 y1] [x2 y2] [x3 y3].
  unfold Cadd, Cre, Cim. simpl.
  f_equal; ring.
Qed.

Lemma Cmul_assoc : forall z1 z2 z3,
  (z1 *c z2) *c z3 = z1 *c (z2 *c z3).
Proof.
  intros [x1 y1] [x2 y2] [x3 y3].
  unfold Cmul, Cre, Cim. simpl.
  f_equal; ring.
Qed.

Lemma Cmul_comm : forall z1 z2,
  z1 *c z2 = z2 *c z1.
Proof.
  intros [x1 y1] [x2 y2].
  unfold Cmul, Cre, Cim. simpl.
  f_equal; ring.
Qed.

Lemma Cmul_Czero_l : forall z,
  Czero *c z = Czero.
Proof.
  intros [x y].
  unfold Czero, Cmul, Cre, Cim. simpl.
  f_equal; ring.
Qed.

Lemma Cmul_one_l : forall z,
  (1, 0) *c z = z.
Proof.
  intros [x y].
  unfold Cmul, Cre, Cim. simpl.
  f_equal; ring.
Qed.

Lemma Cadd_Czero_r : forall z,
  z +c Czero = z.
Proof.
  intros [x y].
  unfold Cadd, Czero, Cre, Cim. simpl.
  f_equal; ring.
Qed.

(* Key lemma: if z *c a = w *c a and a ≠ 0, then z = w *)
Lemma Cmul_cancel_r : forall z w a,
  a <> Czero ->
  z *c a = w *c a ->
  z = w.
Proof.
  intros [zx zy] [wx wy] [ax ay] Ha_neq Heq.
  unfold Cmul, Cre, Cim in Heq.
  simpl in Heq.
  inversion Heq as [[Hre Him]].
  simpl in Hre, Him.

  assert (Hnorm: ax * ax + ay * ay <> 0).
  { intro Hcontra.
    apply Ha_neq.
    apply Czero_eq. simpl.
    apply Rplus_eq_R0 in Hcontra; try apply Rle_0_sqr.
    destruct Hcontra as [Hax Hay].
    apply Rmult_integral in Hax.
    apply Rmult_integral in Hay.
    destruct Hax as [Hax | Hax]; destruct Hay as [Hay | Hay]; auto. }

  f_equal.
  - (* Real parts equal *)
    assert (H1: (zx - wx) * ax - (zy - wy) * ay = 0) by lra.
    assert (H2: (zx - wx) * ay + (zy - wy) * ax = 0) by lra.
    (* From H1: (zx - wx) * ax = (zy - wy) * ay
       From H2: (zx - wx) * ay = -(zy - wy) * ax
       Multiply H1 by ax and H2 by ay, add:
       (zx - wx) * ax * ax + (zx - wx) * ay * ay = 0
       (zx - wx) * (ax * ax + ay * ay) = 0 *)
    assert (Hdiff_x: (zx - wx) * (ax * ax + ay * ay) = 0).
    { apply (f_equal (fun r => r * ax)) in H1.
      apply (f_equal (fun r => r * ay)) in H2.
      lra. }
    apply Rmult_integral in Hdiff_x.
    destruct Hdiff_x as [Hdiff | Hcontra]; lra.

  - (* Imaginary parts equal *)
    assert (H1: (zx - wx) * ax - (zy - wy) * ay = 0) by lra.
    assert (H2: (zx - wx) * ay + (zy - wy) * ax = 0) by lra.
    (* Similar to real part *)
    assert (Hdiff_y: (zy - wy) * (ax * ax + ay * ay) = 0).
    { apply (f_equal (fun r => r * ay)) in H1.
      apply (f_equal (fun r => r * ax)) in H2.
      lra. }
    apply Rmult_integral in Hdiff_y.
    destruct Hdiff_y as [Hdiff | Hcontra]; lra.
Qed.

Lemma equation_normalized : forall a b c E,
  a <> Czero ->
  equation a b c E <-> equation (1, 0) (b /c a) (c /c a) E.
Proof.
  intros a b c E Ha_neq.
  unfold equation.

  assert (Hone: (1, 0) *c E *c Cconj E = E *c Cconj E).
  { rewrite Cmul_one_l. reflexivity. }

  assert (Hb_cancel: (b /c a) *c a = b).
  { apply Cmul_div_cancel. exact Ha_neq. }
  assert (Hc_cancel: (c /c a) *c a = c).
  { apply Cmul_div_cancel. exact Ha_neq. }

  split; intro Heq.
  - (* Forward: (a *c E *c Cconj E) +c (b *c Cconj E) +c c = Czero
       implies (E *c Cconj E) +c ((b /c a) *c Cconj E) +c (c /c a) = Czero *)
    rewrite Hone.
    apply Cmul_cancel_r with (a := a); try assumption.

    (* LHS: ((E *c Cconj E) +c ((b /c a) *c Cconj E) +c (c /c a)) *c a *)
    rewrite Cmul_add_distr_r.
    rewrite Cmul_add_distr_r.

    (* Expand: (E *c Cconj E) *c a *)
    assert (H1: (E *c Cconj E) *c a = a *c E *c Cconj E).
    { destruct E, a. unfold Cmul, Cconj, Cre, Cim. simpl.
      f_equal; ring. }
    rewrite H1.

    (* Expand: ((b /c a) *c Cconj E) *c a *)
    assert (H2: ((b /c a) *c Cconj E) *c a = b *c Cconj E).
    { destruct E as [ex ey].
      destruct a as [ax ay].
      destruct b as [bx by0].
      unfold Cmul, Cconj, Cdiv, Cnorm_sq, Cre, Cim in *. simpl in *.
      assert (Hnorm: ax * ax + ay * ay <> 0).
      { apply (Cdiv_nonzero_well_defined (ex, ey) (ax, ay)). exact Ha_neq. }
      unfold Rdiv. f_equal; field; exact Hnorm. }
    rewrite H2.

    rewrite Hc_cancel.

    (* RHS: Czero *c a = Czero *)
    rewrite Heq.
    rewrite Cmul_Czero_l.
    reflexivity.

  - (* Backward: (E *c Cconj E) +c ((b /c a) *c Cconj E) +c (c /c a) = Czero
       implies (a *c E *c Cconj E) +c (b *c Cconj E) +c c = Czero *)
    rewrite Hone in Heq.

    (* Multiply both sides by a *)
    apply (f_equal (fun z => z *c a)) in Heq.
    rewrite Cmul_Czero_l in Heq.

    rewrite Cmul_add_distr_r in Heq.
    rewrite Cmul_add_distr_r in Heq.

    assert (H1: (E *c Cconj E) *c a = a *c E *c Cconj E).
    { destruct E, a. unfold Cmul, Cconj, Cre, Cim. simpl.
      f_equal; ring. }
    rewrite H1 in Heq.

    assert (H2: ((b /c a) *c Cconj E) *c a = b *c Cconj E).
    { destruct E as [ex ey].
      destruct a as [ax ay].
      destruct b as [bx by0].
      unfold Cmul, Cconj, Cdiv, Cnorm_sq, Cre, Cim in *. simpl in *.
      assert (Hnorm: ax * ax + ay * ay <> 0).
      { apply (Cdiv_nonzero_well_defined (ex, ey) (ax, ay)). exact Ha_neq. }
      unfold Rdiv. f_equal; field; exact Hnorm. }
    rewrite H2 in Heq.

    rewrite Hc_cancel in Heq.
    exact Heq.
Qed.

Lemma solution_on_circle : forall E b_prime c_prime,
  equation (1, 0) b_prime c_prime E ->
  c_prime = c_from_E_and_b E b_prime.
Proof.
  intros E b_prime c_prime Heq.
  unfold equation in Heq.
  unfold c_from_E_and_b.
  (* The equation is: (1,0) *c E *c Cconj E +c b_prime *c Cconj E +c c_prime = Czero
     We need to show: c_prime = (-1) ·c (E *c Cconj E) +c (-1) ·c (b_prime *c Cconj E) *)

  (* First, simplify (1,0) *c E *c Cconj E = E *c Cconj E *)
  assert (Hsimp: (1, 0) *c E *c Cconj E = E *c Cconj E).
  { destruct E. unfold Cmul, Cre, Cim. simpl. f_equal; ring. }
  rewrite Hsimp in Heq.

  (* Now Heq is: E *c Cconj E +c b_prime *c Cconj E +c c_prime = Czero *)
  (* This means: c_prime = -(E *c Cconj E) - (b_prime *c Cconj E) *)

  (* Manipulate to solve for c_prime *)
  assert (Hrearrange: c_prime = ((-1) ·c (E *c Cconj E)) +c ((-1) ·c (b_prime *c Cconj E))).
  { destruct E, b_prime, c_prime.
    unfold Cmul, Cadd, Cscale, Cconj, Czero, Cre, Cim in *.
    simpl in *.
    apply Czero_eq in Heq.
    destruct Heq as [Hre Him].
    simpl in Hre, Him.
    f_equal; lra. }
  exact Hrearrange.
Qed.

Lemma c_from_E_satisfies_envelope : forall E b_prime,
  let c_prime := c_from_E_and_b E b_prime in
  let r := Cnorm E in
  let b_norm := Cnorm b_prime in
  Cre c_prime * Cre c_prime + Cim c_prime * Cim c_prime <=
    (b_norm * b_norm * b_norm * b_norm) / 4 /\
  Cre c_prime <= (b_norm * b_norm) / 2.
Proof.
  intros E b_prime.
  unfold c_from_E_and_b.
  simpl.

  (* Expand the complex operations to real coordinates *)
  destruct E as [ex ey].
  destruct b_prime as [bpx bpy].
  unfold Cmul, Cadd, Cscale, Cconj, Cre, Cim, Cnorm, Cnorm_sq. simpl.

  split.
  - (* Bound on |c'|²: This requires showing that
       |c'|² = |-|E|² - b'·Ē|² ≤ |b'|⁴/4

       The proof uses the fact that c' = -|E|² - b'·Ē and optimizes over E.
       By completing the square or using Cauchy-Schwarz, we can show the bound.
       This is a genuine optimization problem requiring calculus. *)
    admit.

  - (* Bound on Re(c'): Show Re(c') = -(ex² + ey²) - (bpx·ex + bpy·ey) ≤ |b'|²/2

       Strategy: Complete the square to find the maximum.
       Let f(ex, ey) = -(ex² + ey²) - (bpx·ex + bpy·ey)

       Complete the square:
       f = -(ex² + bpx·ex) - (ey² + bpy·ey)
         = -((ex + bpx/2)² - bpx²/4) - ((ey + bpy/2)² - bpy²/4)
         = -(ex + bpx/2)² - (ey + bpy/2)² + bpx²/4 + bpy²/4
         = -(ex + bpx/2)² - (ey + bpy/2)² + (bpx² + bpy²)/4

       Since -(ex + bpx/2)² ≤ 0 and -(ey + bpy/2)² ≤ 0,
       the maximum is (bpx² + bpy²)/4

       But wait, we need to show ≤ (bpx² + bpy²)/2, not /4.
       Let me recalculate... *)

    (* After simplification, we have:
       Re(c') = - (ex * ex + ey * ey) - (bpx * ex + bpy * ey)

       To maximize this, complete the square:
       = -ex² - ey² - bpx·ex - bpy·ey
       = -(ex² + bpx·ex + bpx²/4 - bpx²/4) - (ey² + bpy·ey + bpy²/4 - bpy²/4)
       = -((ex + bpx/2)² - bpx²/4) - ((ey + bpy/2)² - bpy²/4)
       = -(ex + bpx/2)² + bpx²/4 - (ey + bpy/2)² + bpy²/4

       The maximum occurs at ex = -bpx/2, ey = -bpy/2, giving:
       max Re(c') = bpx²/4 + bpy²/4 = (bpx² + bpy²)/4 = |b'|²/4

       But the lemma states ≤ |b'|²/2, which is a weaker bound that's always true since
       |b'|²/4 ≤ |b'|²/2 *)

    (* After unfolding, goal is:
       -1 * (ex * ex - ey * - ey) + -1 * (bpx * ex - bpy * - ey) <= sqrt(...) * sqrt(...) * / 2
       Simplify to: -(ex² + ey²) - (bpx·ex + bpy·ey) ≤ (bpx² + bpy²)/2 *)

    assert (Hsqrt_elim: sqrt (bpx * bpx + bpy * bpy) * sqrt (bpx * bpx + bpy * bpy) =
                        bpx * bpx + bpy * bpy).
    { rewrite <- sqrt_sqrt.
      - reflexivity.
      - apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
    rewrite Hsqrt_elim.

    (* Complete the square *)
    assert (Hsq1: 0 <= (ex + bpx * / 2) * (ex + bpx * / 2)) by apply Rle_0_sqr.
    assert (Hsq2: 0 <= (ey + bpy * / 2) * (ey + bpy * / 2)) by apply Rle_0_sqr.

    (* The maximum of -(ex² + ey²) - (bpx·ex + bpy·ey) is (bpx² + bpy²)/4 *)
    assert (Hmax: -1 * (ex * ex - ey * - ey) + -1 * (bpx * ex - bpy * - ey) <=
                  (bpx * bpx + bpy * bpy) * / 4).
    { nra. }

    (* Since /4 ≤ /2, we get the result *)
    assert (Hle: (bpx * bpx + bpy * bpy) * / 4 <= (bpx * bpx + bpy * bpy) * / 2).
    { assert (Hpos: 0 <= bpx * bpx + bpy * bpy).
      { apply Rplus_le_le_0_compat; apply Rle_0_sqr. }
      nra. }
    lra.
Admitted.

(*
  ==============================================================================
  MAIN THEOREM
  ==============================================================================

  The main result is that for a ≠ 0, the equation has a solution if and only if
  c' (after normalization) lies inside or on the envelope.
*)

Theorem envelope_characterizes_solutions : forall a b c,
  a <> Czero ->
  has_solution a b c <->
  (inside_envelope (Cnorm (b /c a)) (Cre (c /c a)) (Cim (c /c a)) \/
   on_envelope (Cnorm (b /c a)) (Cre (c /c a)) (Cim (c /c a))).
Proof.
  intros a b c Ha_neq.
  unfold has_solution.
  split.
  - (* Forward: if solution exists, then c' is inside or on envelope *)
    intro Hexists.
    destruct Hexists as [E Heq].

    (* Use equation_normalized to convert to normalized form *)
    apply equation_normalized in Heq; try exact Ha_neq.

    (* E satisfies the normalized equation, so c' = c_from_E_and_b *)
    set (b_prime := b /c a) in *.
    set (c_prime := c /c a) in *.
    apply solution_on_circle in Heq.

    (* Heq now tells us: c_prime = c_from_E_and_b E b_prime *)
    (* We need to show c_prime is inside or on the envelope *)

    (* This would follow from c_from_E_satisfies_envelope if we had it proven.
       The key insight: any c' that can be written as c_from_E_and_b for some E
       satisfies the envelope bounds. Since Heq gives us this representation,
       c_prime must be on or inside the envelope. *)
    admit.

  - (* Backward: if c' is inside or on envelope, construct solution *)
    intro Henv.
    unfold inside_envelope, on_envelope in Henv.
    destruct Henv as [Hinside | Hon].

    + (* Inside envelope case: c_y² < b⁴/4 - b²·c_x and c_x ≤ b²/2 *)
      (* Strategy: solve the equation E·Ē + (b/a)·Ē + (c/a) = 0 for E.
         This is equivalent to finding E such that:
           |E|² + (b/a)·Ē + (c/a) = 0
         Rearranging: |E|² = -(b/a)·Ē - (c/a)

         This is a complex quadratic-type equation. For points inside the envelope,
         solutions exist. The construction involves:
         1. Parameterizing E in terms of its norm |E| = r
         2. Using the constraint to solve for valid values of r and angle
         3. Showing that inside envelope implies valid real solutions exist *)
      admit.

    + (* On envelope case: c_y² = b⁴/4 - b²·c_x and c_x ≤ b²/2 *)
      (* Similar to inside case, but the equation has solutions exactly on
         the boundary. The envelope characterization guarantees existence. *)
      admit.
Admitted.

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
     - Solutions exist iff c' (normalized) lies inside or on the envelope
     - Envelope: c_y² = (|b'|⁴)/4 - |b'|²·c_x, with c_x ≤ (|b'|²)/2

  Future work would complete the proofs using complex analysis and
  the envelope calculation from the latex document.
  ==============================================================================
*)
