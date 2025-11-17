Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition on_envelope (b_norm c_x c_y : R) : Prop :=
  c_y * c_y = (b_norm * b_norm * b_norm * b_norm) / 4 -
              (b_norm * b_norm) * c_x /\
  c_x <= (b_norm * b_norm) / 2.

(* Test different proof strategies *)

(* Strategy 1: Direct ring *)
Lemma envelope_symmetric_v1 : forall b_norm c_x c_y,
  on_envelope b_norm c_x c_y ->
  on_envelope b_norm c_x (-c_y).
Proof.
  intros b_norm c_x c_y [Heq Hleq].
  unfold on_envelope.
  split; [| exact Hleq].
  rewrite <- Heq.
  ring.
Qed.

(* Strategy 2: Using Rmult_opp_opp *)
Lemma envelope_symmetric_v2 : forall b_norm c_x c_y,
  on_envelope b_norm c_x c_y ->
  on_envelope b_norm c_x (-c_y).
Proof.
  intros b_norm c_x c_y [Heq Hleq].
  unfold on_envelope.
  split; [| exact Hleq].
  rewrite Rmult_opp_opp.
  exact Heq.
Qed.

(* Strategy 3: Field simplify *)
Lemma envelope_symmetric_v3 : forall b_norm c_x c_y,
  on_envelope b_norm c_x c_y ->
  on_envelope b_norm c_x (-c_y).
Proof.
  intros b_norm c_x c_y [Heq Hleq].
  unfold on_envelope.
  split; [| exact Hleq].
  rewrite <- Heq.
  field.
Qed.
