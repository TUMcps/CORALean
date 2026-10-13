import CORALean.ContDynamics.LinearSys.Operations.MinBackReachInitFloat
import CORALean.ContDynamics.LinearSys.Operations.MinBackReachStepFloat

/-!
# `Alg. 1` lines 6-13 in floats: the loop

`minBackReachRun` computed in `𝕋`: [1, Alg. 1] lines 6-13, the state after the first `k`
iterations; `0` is the pre-loop state of lines 1-6, so the `k`-th iteration's set is `run
(k+1)`'s.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 6-13: the state after the first `k` iterations. -/
def LinearSys.minBackReachRunFloat (sys : LinearSys 𝕋 n) (CZ : ConZonotope 𝕋 (Vec 𝕋 n))
    (W₀ U₀ : Zonotope (Vec 𝕋 n)) (Zw : 𝕋 → Zonotope (Vec 𝕋 n)) (t₀ Δt : 𝕋) (η ν : ℕ) :
    ℕ → LinearSys.MinBackReachStateOf 𝕋 (Zonotope (Vec 𝕋 n)) (ConZonotope 𝕋 (Vec 𝕋 n))
  | 0 => sys.minBackReachInitFloat W₀ U₀ t₀ η
  | k + 1 => sys.minBackReachStepFloat CZ W₀ U₀ Zw Δt η ν
      (sys.minBackReachRunFloat CZ W₀ U₀ Zw t₀ Δt η ν k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
