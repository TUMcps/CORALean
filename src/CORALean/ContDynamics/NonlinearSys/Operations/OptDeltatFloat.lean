module

public import CORALean.ContDynamics.NonlinearSys.Definitions.OptStep
public import CORALean.ContDynamics.NonlinearSys.Operations.OptDeltatSearchFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.ReachSizeEstimateFloat

@[expose] public section

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
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] line 10: eq. (58)'s optimal time step size, and the `λ'` it was
found at. -/
def optDeltatFloat [SoundFloatArithmetic 𝕋] [ToRat 𝕋] (prec bis : ℕ)
    (ζδ ζZ ζA φ1 r₀ rabs h : 𝕋) (fuel : ℕ) :
    NonlinearSys.OptStep 𝕋 :=
  -- 10. eq. (57): the cost function
  let cost := reachSizeEstimateFloat prec bis ζδ ζZ ζA φ1 r₀ rabs
  -- 10. eq. (58): the argmin over λ'
  let sstar := optDeltatSearchFloat cost 0 fuel
  -- 10. eq. (58): Δt* = h ζ_δ^{λ'}
  ⟨mulUp h (powUp ζδ sstar), sstar⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
