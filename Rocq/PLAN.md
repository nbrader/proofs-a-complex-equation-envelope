## Next steps to finish the Coquelicot proof

1. **Fix the `br = 0` branch of `construct_E_from_envelope_point`.**  
   The current choice `y := sqrt y_sq` always picks the non‑negative root, so the equality `sqrt y_sq = bi'/2` only holds when `Im b' ≥ 0`.  Update the construction to incorporate the sign of `Im b'` (for instance, define `y := sign(bi') * sqrt y_sq` or destruct `Rtotal_order bi' 0`), then adjust the follow‑up algebra so that both the real and imaginary equations go through without assuming `bi' ≥ 0`.

2. **Propagate the signed choice through the rest of the lemma.**  
   After redefining `y`, revisit the proof steps that use `Hy_value` and confirm they no longer depend on the discarded assumption.  This may require a short case analysis when cancelling factors or applying `Rsqr_inj`.

3. **Rebuild `ComplexEnvelope_Coquelicot.v` and fix any subsequent obligations.**  
   Run `coqc -Q . ComplexEnvelope ComplexEnvelope_Coquelicot.v`.  If new errors arise deeper in the file (e.g., in the `br ≠ 0` branch or the “inside envelope” lemma), repeat the same process: isolate the exact algebraic fact needed, keep reasoning in `R`, and insert the appropriate `RtoC` casts only at the end.

4. **Document the completion.**  
   Once the file compiles, update `README_COQUELICOT.md` with a short note that the latex argument is now fully formalized via `ComplexEnvelope_Coquelicot.v`, and consider adding CI instructions (running `coqc` or `dune build`) so future contributors can reproduce the check.
