# ComplexEnvelope - Coquelicot Version

This directory contains both the original custom implementation and a new Coquelicot-based version of the complex envelope proofs.

## Files

- **`ComplexEnvelope.v`** - Original version with custom complex number implementation
  - ✅ Fully proven: a = 0 case
  - ⚠️ Admitted: geometric construction, division-based normalization
  - Status: Good foundation, but lacks division operator

- **`ComplexEnvelope_Coquelicot.v`** - New version using Coquelicot library
  - ✅ Fully proven: a = 0 case, scaling lemmas
  - ⭐ Has division: Proper normalization `b' = b/a`
  - ⚠️ Admitted: geometric construction (but strategy is clear)
  - Status: Ready to complete remaining admits

- **`GEOMETRIC_CONSTRUCTION.md`** - Detailed strategy for completing proofs
- **`ComplexEnvelope_Coquelicot_Example.v`** - Original example/sketch

## Installation

### Prerequisites

```bash
# Install Coq/Rocq (if not already installed)
opam install coq

# Install Coquelicot
opam install coq-coquelicot
```

### Verify Installation

```bash
coqc -Q . ComplexEnvelope -R "$(opam var lib)/coq/user-contrib/Coquelicot" Coquelicot \
  ComplexEnvelope_Coquelicot.v
```

## Building

### Option 1: Using coqc directly

```bash
# Compile the Coquelicot version
coqc -Q . ComplexEnvelope \
     -R "$(opam var lib)/coq/user-contrib/Coquelicot" Coquelicot \
     ComplexEnvelope_Coquelicot.v
```

### Option 2: Using _CoqProject

Add to `_CoqProject`:
```
-Q . ComplexEnvelope
-R <path-to-coquelicot> Coquelicot

ComplexEnvelope_Coquelicot.v
```

Then:
```bash
coq_makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
```

### Option 3: Using Dune

Update `dune`:
```lisp
(coq.theory
 (name ComplexEnvelope)
 (package coq-complex-envelope)
 (theories Coquelicot))
```

Then:
```bash
dune build
```

## Differences Between Versions

| Feature | ComplexEnvelope.v | ComplexEnvelope_Coquelicot.v |
|---------|-------------------|------------------------------|
| **Complex division** | ❌ Not defined | ✅ `Cdiv` from Coquelicot |
| **Normalization** | ⚠️ `b = a *c b'` workaround | ✅ `b' = b / a` directly |
| **Field tactics** | ❌ Manual algebra | ✅ `field` tactic |
| **Case a = 0** | ✅ Complete | ✅ Complete |
| **Scaling lemma** | ✅ Proven (manual) | ✅ Proven (with `field`) |
| **Geometric construction** | ⚠️ Admitted | ⚠️ Admitted (but clearer strategy) |
| **Main theorem** | ⚠️ Has formalization gap | ✅ Correct statement |

## Current Status

### ComplexEnvelope_Coquelicot.v

**✅ Fully Proven (203 lines):**
- Case a = 0 (all subcases)
- `scale_equation_by_a` - Scaling property
- `envelope_symmetric` - Envelope symmetry
- `compute_z_from_envelope` - Extract |E| from envelope

**⚠️ Admitted (3 admits, ~30-40 lines each to complete):**

1. **`construct_E_from_envelope_point`** - Geometric construction
   - Strategy: Algebraic (quadratic formula)
   - Difficulty: Medium (careful case analysis)
   - Estimated: 3-4 hours
   - See: `GEOMETRIC_CONSTRUCTION.md`

2. **`envelope_characterizes_solutions` (forward)** - Solution → envelope
   - Strategy: Geometric analysis of parameterization
   - Difficulty: Medium
   - Estimated: 2-3 hours

3. **`envelope_characterizes_solutions` (inside case)** - Inside envelope → solution
   - Strategy: Similar to "on envelope" case
   - Difficulty: Low (adapt existing proof)
   - Estimated: 1-2 hours

**Total estimated effort to complete: 6-9 hours**

## Advantages of Coquelicot Version

1. **Division operator** - No formalization gap, correct statements
2. **Field tactics** - Automatic algebraic simplification
3. **Analysis tools** - IVT, continuity, derivatives available if needed
4. **Mature library** - Well-tested, documented
5. **Standard approach** - Uses community-accepted library

## Recommended Workflow

If you want to complete all proofs:

1. **Start with Coquelicot version** - `ComplexEnvelope_Coquelicot.v`
2. **Follow construction guide** - `GEOMETRIC_CONSTRUCTION.md`
3. **Use algebraic strategy** - Quadratic formula approach
4. **Verify with original** - Compare with custom implementation

If you want to keep custom implementation:

1. **Define complex division** - Add `Cinv` and `Cdiv` to `ComplexEnvelope.v`
2. **Prove field axioms** - ~10-15 hours of work
3. **Then use similar structure** - Follow Coquelicot version as guide

## Mathematical Content

Both files formalize the same mathematical theorem:

**Theorem:** The equation `a·E·Ē + b·Ē + c = 0` has a solution `E ∈ ℂ` if and only if:

- When `a = 0`: `b ≠ 0` OR (`b = 0` AND `c = 0`)

- When `a ≠ 0`: The normalized point `c' = c/a` satisfies:
  ```
  Im(c')² ≤ |b/a|⁴/4 - |b/a|²·Re(c')
  Re(c') ≤ |b/a|²/2
  ```

This characterizes the **envelope** of the family of circles in the `c'` plane parameterized by `|E|`.

## References

- **Coquelicot Documentation:** http://coquelicot.saclay.inria.fr/html/
- **Coquelicot Complex Module:** http://coquelicot.saclay.inria.fr/html/Coquelicot.Complex.html
- **Original LaTeX Proof:** `../Proof/proof.tex`
- **Project README:** `../README.md`

## Questions?

Check:
1. `GEOMETRIC_CONSTRUCTION.md` for proof strategies
2. `LIBRARY_INTEGRATION.md` for migration guidance
3. Comments in `ComplexEnvelope_Coquelicot.v` for inline documentation
