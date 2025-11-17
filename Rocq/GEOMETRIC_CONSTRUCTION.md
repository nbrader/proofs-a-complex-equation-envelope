# Completing the Geometric Construction

This document explains how to complete the remaining admitted proofs in `ComplexEnvelope_Coquelicot.v`, particularly the core geometric construction `construct_E_from_envelope_point`.

## The Problem

Given:
- `b_prime = (br, bi)` with `|b_prime| ≠ 0`
- `c_prime = (cr, ci)` on the envelope

Find: `E = (x, y)` such that `E·Ē + b_prime·Ē + c_prime = 0`

This translates to the system:
```
x² + y² + br·x - bi·y + cr = 0  (real part)
bi·x - br·y + ci = 0            (imaginary part)
```

## Strategy 1: Algebraic Construction (Recommended)

### Step 1: Compute `z²` from envelope

From the envelope condition: `z² = (|b'|²)/2 - cr`

This is already proven in `compute_z_from_envelope`.

### Step 2: Case analysis on `br` and `bi`

#### Case 2a: `br ≠ 0`

From the imaginary constraint: `y = (bi·x + ci) / br`

Substitute into `x² + y² = z²`:

```
x² + ((bi·x + ci) / br)² = z²
```

Multiply by `br²`:
```
br²·x² + (bi·x + ci)² = br²·z²
(br² + bi²)·x² + 2·bi·ci·x + ci² = br²·z²
```

This is a quadratic in `x`:
```
A·x² + B·x + C = 0
where:
  A = br² + bi² = |b'|²
  B = 2·bi·ci
  C = ci² - br²·z²
```

**Discriminant:**
```
Δ = B² - 4AC
  = 4·bi²·ci² - 4·(br² + bi²)·(ci² - br²·z²)
  = 4·bi²·ci² - 4·(br² + bi²)·ci² + 4·(br² + bi²)·br²·z²
  = -4·br²·ci² + 4·|b'|²·br²·z²
  = 4·br²·(|b'|²·z² - ci²)
```

**Key envelope property:**
From the envelope equation: `ci² = |b'|⁴/4 - |b'|²·cr`

And `z² = |b'|²/2 - cr`, so:
```
|b'|²·z² = |b'|²·(|b'|²/2 - cr) = |b'|⁴/2 - |b'|²·cr

Therefore:
|b'|²·z² - ci² = (|b'|⁴/2 - |b'|²·cr) - (|b'|⁴/4 - |b'|²·cr)
                = |b'|⁴/4
```

So: `Δ = 4·br²·|b'|⁴/4 = br²·|b'|⁴ ≥ 0` ✓

**Solutions:**
```
x = (-B ± √Δ) / (2A)
  = (-2·bi·ci ± br·|b'|²) / (2·|b'|²)
  = (-bi·ci ± br·|b'|²/2) / |b'|²
```

Then: `y = (bi·x + ci) / br`

#### Case 2b: `br = 0, bi ≠ 0`

Similar analysis, swapping roles of `x` and `y`.

From imaginary constraint: `x = ci / bi`

Substitute into `x² + y² = z²`:
```
(ci/bi)² + y² = z²
y² = z² - ci²/bi²
```

Must verify `z² - ci²/bi² ≥ 0` (follows from envelope).

### Step 3: Coq Implementation

```coq
Lemma construct_E_from_envelope_point_algebraic :
  forall b_prime c_prime,
  Cmod b_prime <> 0 ->
  on_envelope (Cmod b_prime) (Re c_prime) (Im c_prime) ->
  exists E : C,
    equation C1 b_prime c_prime E.
Proof.
  intros b_prime c_prime Hb_nonzero Hon.

  set (br := Re b_prime).
  set (bi := Im b_prime).
  set (cr := Re c_prime).
  set (ci := Im c_prime).

  (* Compute z² *)
  destruct (compute_z_from_envelope ...) as [z [Hz_nonneg Hz_sq]].

  (* Case split: br ≠ 0 or br = 0 *)
  destruct (Req_dec br 0) as [Hbr_zero | Hbr_nonzero].

  - (* Case: br = 0, so bi ≠ 0 *)
    (* Prove bi ≠ 0 from |b'| ≠ 0 and br = 0 *)
    assert (Hbi_nonzero : bi <> 0).
    { (* proof *) }

    (* x = ci / bi *)
    set (x := ci / bi).

    (* y² = z² - x² *)
    set (y_sq := z * z - x * x).

    (* Prove y_sq ≥ 0 from envelope *)
    assert (Hy_sq_nonneg : y_sq >= 0).
    { (* use envelope equation *) }

    (* Take y = ±√y_sq *)
    set (y := sqrt y_sq).

    exists (x, y).
    (* Verify equation *)

  - (* Case: br ≠ 0 *)
    (* Quadratic formula *)
    set (A := br * br + bi * bi).
    set (B := 2 * bi * ci).
    set (C := ci * ci - br * br * z * z).
    set (Delta := B * B - 4 * A * C).

    (* Prove Δ = br²·|b'|⁴ *)
    assert (HDelta : Delta = br * br * A * A).
    { unfold Delta, A, B, C.
      (* Use envelope equation to simplify *)
      admit. }

    (* Δ ≥ 0 *)
    assert (HDelta_nonneg : Delta >= 0).
    { rewrite HDelta.
      apply Rmult_le_pos; apply Rle_0_sqr. }

    (* x = (-B + √Δ) / (2A) *)
    set (x := (- B + sqrt Delta) / (2 * A)).

    (* y = (bi·x + ci) / br *)
    set (y := (bi * x + ci) / br).

    exists (x, y).
    (* Verify equation holds *)
Qed.
```

## Strategy 2: Using Circle-Line Intersection Lemma

If you have access to a geometry library (like GeoCoq), you can use:

```coq
Lemma circle_line_intersection :
  forall (r : R) (a b c : R),
  r > 0 ->
  a * a + b * b <> 0 ->
  let d := |c| / sqrt(a² + b²) in
  d <= r ->
  exists x y,
    x² + y² = r² /\
    a·x + b·y + c = 0.
```

Apply this with:
- Circle: `x² + y² = z²` (radius `z`)
- Line: `bi·x - br·y + ci = 0`
- Distance from origin to line: `|ci| / √(br² + bi²) = |ci| / |b'|`

The envelope condition guarantees `distance ≤ radius`.

## Strategy 3: Classical + IVT (Using Coquelicot)

For a non-constructive proof:

```coq
(* Define f(θ) = imaginary constraint evaluated at E = z·(cos θ, sin θ) *)
Definition f (theta : R) : R :=
  bi * (z * cos theta) - br * (z * sin theta) + ci.

(* f is continuous *)
Lemma f_continuous : ...

(* f(0) and f(π) have opposite signs (or one is zero) *)
Lemma f_ivt_condition : ...

(* By IVT, exists θ₀ with f(θ₀) = 0 *)
Lemma exists_theta : exists theta, f theta = 0.

(* Define E = z·(cos θ₀, sin θ₀) *)
```

This approach requires:
- Coquelicot's `is_lim` and continuity framework
- IVT: `Coq.Reals.Ranalysis5.IVT`
- Trigonometric functions from `Reals.Rtrigo`

## Recommended Approach

**For this project: Strategy 1 (Algebraic)**

Advantages:
- ✅ Self-contained
- ✅ Constructive
- ✅ No additional dependencies
- ✅ Clear mathematical content

Estimated effort: 3-4 hours for careful proof

**Alternative: Strategy 3 (Classical + IVT)**

Advantages:
- ✅ Shorter proof
- ✅ Uses Coquelicot's analysis tools
- ⚠️ Non-constructive

Estimated effort: 2-3 hours

## Next Steps

1. **Implement Strategy 1** - Complete algebraic construction
2. **Prove envelope property** - Show `Δ = br²·|b'|⁴`
3. **Handle edge cases** - `br = 0` or `bi = 0`
4. **Verify equation** - Substitute back and simplify

All the mathematical content is sound. The proof is just careful algebra + case analysis.
