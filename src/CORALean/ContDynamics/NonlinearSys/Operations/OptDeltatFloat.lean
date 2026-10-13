import CORALean.ContDynamics.NonlinearSys.Operations.OptDeltatSearchFloat
import CORALean.ContDynamics.NonlinearSys.Operations.ReachSizeEstimateFloat

/-!
# `optDeltat`: the time step size that balances the two wrapping effects, in floats

`optDeltat` in `𝕋`. Tuning only: the value picks a step size, an order or a gain and no soundness
statement reads it, so every rounding is upward and no theorem is owed. What a run guarantees
holds for whatever this returns. See [1].

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] line 10: eq. (58)'s optimal time step size, and the `λ'` it was
found at. -/
def optDeltatFloat [SoundFloatArithmetic 𝕋] [ToRat 𝕋] (prec bis : ℕ)
    (ζδ ζZ ζA φ1 r₀ rabs h : 𝕋) (fuel : ℕ) : 𝕋 × ℕ :=
  let cost := reachSizeEstimateFloat prec bis ζδ ζZ ζA φ1 r₀ rabs  -- 57. the cost function
  let sstar := optDeltatSearchFloat cost 0 fuel                  -- 58. the argmin over λ'
  (mulUp h (powUp ζδ sstar), sstar)                              -- 58. Δt* = h ζ_δ^{λ'}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
