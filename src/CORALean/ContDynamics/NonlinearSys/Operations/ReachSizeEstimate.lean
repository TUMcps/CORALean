module

public import CORALean.ContDynamics.NonlinearSys.Operations.InterpGain
public import CORALean.Global.Tensor
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Eq. (57): the estimated size after a finite horizon

`reachSizeEstimate`: the size `R(t)` is estimated to reach after the finite
horizon, walked in `λ = ζ_δ^{-λ'}` steps. Scalars throughout, which is [1]'s
own simplification: `r₀` and `r_abs` are the radii of `R(t)` and of
`R_abs(h)`, and `ζ_A = e^{tr(Ah)}` is eq. (50)'s determinant estimate.
Nothing here is a set.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Eq. (57): the size `R(t)` is estimated to reach after the finite horizon,
walked in `λ = ζ_δ^{-λ'}` steps. -/
noncomputable def reachSizeEstimate (ζδ ζZ ζA φ1 r₀ rabs : ℝ) (scalings : ℕ) : ℝ :=
  let lam := (1 / ζδ) ^ scalings                                -- λ = ζ_δ^{-λ'}
  let N := ⌊lam⌋₊                                               -- ⌊λ⌋ whole steps
  let b := lam - (N : ℝ)                                        -- the last incomplete step
  let ζAZ := (∑ j ∈ Finset.Icc 1 N,                             -- 53. ζ_{A,Z}(λ)
      (1 + 2 * ζZ) ^ (b + (j : ℝ)) * ζA ^ ((b + (j : ℝ) - 1) / lam))
    + b * (1 + 2 * ζZ) ^ b
  r₀ * (1 + 2 * ζZ) ^ lam * ζA                                  -- 57. the start set, propagated
    + rabs / lam * ζAZ * ∏ j ∈ Finset.range scalings, interpGain ζδ φ1 j -- 57. errors, accumulated

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
