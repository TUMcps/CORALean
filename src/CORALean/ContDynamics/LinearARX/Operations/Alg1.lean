import CORALean.ContDynamics.LinearARX.Operations.Alg1State

/-!
# Alg. 1: reachability analysis with arbitrary sets

[1, Alg. 1], line 7 of the `m`-th pass: `Ỹ(k:k₊) ← S ⊕ ⊕_{i=0}^{p-1} B̃ᵢ Ũ(k₊ - i)`, the
window of reachable sets at `k = k_init + m p`. The loop bound `k ≤ p + k_h` only says
when to stop, so every pass is defined; `alg1State` carries the rest of the listing.

## References

* [1] L. Lützow and M. Althoff. "Reachability Analysis of ARMAX Models". In Proc. of the
  62nd IEEE Conference on Decision and Control (CDC), 2023, pp. 7027-7034.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearARX.alg1 (sys : LinearARX 𝕋 dy du p) (yinit : Vec ℝ (p * dy))
    (U : ℕ → Set (Vec ℝ du)) (kinit m : ℕ) : Set (Vec ℝ (p * dy)) :=
  let state := sys.alg1State yinit U kinit m
  let k := state.1
  let kplus := k + p - 1
  let S := state.2.1
  let Btilde := state.2.2
  S + ∑ i ∈ Finset.range p, (Btilde i *ᵥ ·) '' U (kplus - i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
