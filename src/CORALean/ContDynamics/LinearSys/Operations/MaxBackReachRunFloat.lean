import CORALean.ContDynamics.LinearSys.Operations.MaxBackReachStepFloat

/-!
# `Alg. 2` lines 6-13 in floats: the state after the first `k` iterations

`maxBackReachRun` computed in `𝕋`: `0` is line 2's pre-loop state, so the `k`-th iteration's set
is `run (k+1)`'s. `none` as soon as one iteration is, or when the order the search raises `η`
to at `t₀` is not the
one it raises it to at `Δt`: the exact run takes one order throughout.
The lines are those of [1, Alg. 2].

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 6-13: the state after the first `k` iterations, from the inside. -/
def LinearSys.maxBackReachRunFloat (sys : LinearSys 𝕋 n) (Bx : Interval (Vec 𝕋 n))
    (P₁ P₂ : HPolytope 𝕋 n) (U W₀ : Zonotope 𝕋 n) (Zw : 𝕋 → 𝕋 → Zonotope 𝕋 n) (t₀ Δt : 𝕋)
    (η : ℕ) : ℕ → Option (LinearSys.MaxBackReachStateFloat 𝕋 n)
  | 0 => if sys.reachOrderFloat t₀ t₀ η = sys.reachOrderFloat Δt Δt η     -- one order throughout
      then sys.maxBackReachInitFloat U W₀ t₀ η else none
  | k + 1 => (sys.maxBackReachRunFloat Bx P₁ P₂ U W₀ Zw t₀ Δt η k).bind
      (sys.maxBackReachStepFloat Bx P₁ P₂ U W₀ Zw Δt η)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
