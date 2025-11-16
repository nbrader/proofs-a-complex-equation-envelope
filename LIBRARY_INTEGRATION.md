# Library Integration Plan for ComplexEnvelope.v

## Current State
- Custom complex number implementation (C = R × R)
- Missing: complex division
- Admitted: geometric construction lemma

## Recommended Approach: Migrate to Coquelicot

### Why Coquelicot?
1. **Solves division gap immediately** - has `Cinv` and `Cdiv` with field theory
2. **User-friendly** - uses total functions, natural notation
3. **Conservative extension** - builds on Coq.Reals (which you already use)
4. **Complete** - includes limits, continuity, analysis tools for geometric reasoning

### Migration Steps

#### Step 1: Install Coquelicot
```bash
opam install coq-coquelicot
```

#### Step 2: Replace Complex Definitions
**Current:**
```coq
Definition C := (R * R)%type.
Definition Cmul (z1 z2 : C) : C := ...
```

**New:**
```coq
Require Import Coquelicot.Coquelicot.
(* C, Cplus, Cmult, Cinv, Cdiv already defined *)
```

#### Step 3: Add Division Operations
```coq
Definition normalize (a b : C) : C := Cdiv b a.

Lemma envelope_with_division : forall a b c,
  a <> C0 ->
  let b_prime := Cdiv b a in
  let c_prime := Cdiv c a in
  has_solution a b c <->
  (inside_envelope (Cmod b_prime) (Re c_prime) (Im c_prime) \/
   on_envelope (Cmod b_prime) (Re c_prime) (Im c_prime)).
```

#### Step 4: Use Analytic Tools for Geometric Construction

Coquelicot provides:
- `is_lim` for limits and continuity
- `Derive` for derivatives
- Intermediate Value Theorem
- Square root lemmas with `sqrt` and `Rsqr_sqrt`

For `construct_E_from_envelope_point`, you can:
1. Express the system as a real polynomial: `f(x) = x² + (linear terms) + constant = 0`
2. Show `f` is continuous
3. Use IVT to prove existence of root
4. Extract `y` from linear constraint

### Alternative: Partial Migration

Keep your custom complex definitions but import just division:
```coq
Require Import Coquelicot.Complex.

(* Define conversion functions *)
Definition to_Coquelicot (z : C) : Coquelicot.C := (Cre z, Cim z).
Definition from_Coquelicot (z : Coquelicot.C) : C := (fst z, snd z).

(* Use Coquelicot for division *)
Definition Cdiv_custom (z1 z2 : C) : C :=
  from_Coquelicot (Cdiv (to_Coquelicot z1) (to_Coquelicot z2)).
```

## For Geometric Construction: GeoCoq (Optional)

If analytic approach is too complex, GeoCoq offers synthetic geometry:

```coq
Require Import GeoCoq.Tarski_dev.Annexes.circles.

(* Use circle-line intersection theorems *)
Lemma line_circle_intersection : forall A B P r,
  (* conditions *)
  exists I1 I2, OnCirc I1 P r /\ OnCirc I2 P r /\ OnLine I1 A B /\ OnLine I2 A B.
```

## Effort Estimates

| Approach | Division Gap | Geometric Construction | Total Effort |
|----------|--------------|------------------------|--------------|
| **Full Coquelicot** | 2-3 hours | 4-6 hours | 6-9 hours |
| **Partial + Custom** | 3-4 hours | 6-8 hours | 9-12 hours |
| **Keep Custom + GeoCoq** | 5-7 hours | 3-5 hours | 8-12 hours |

**Recommendation: Full Coquelicot migration** - cleanest, most maintainable, leverages mature library.

## Next Steps

1. Create new branch: `git checkout -b feature/coquelicot-integration`
2. Install Coquelicot: `opam install coq-coquelicot`
3. Create `ComplexEnvelope_Coquelicot.v` alongside current file
4. Migrate definitions incrementally
5. Port proven lemmas first, then tackle admitted ones

## Resources

- Coquelicot Documentation: http://coquelicot.saclay.inria.fr/html/
- Coquelicot Paper: https://www.lri.fr/~melquion/doc/14-mcs.pdf
- Complex Module: http://coquelicot.saclay.inria.fr/html/Coquelicot.Complex.html
