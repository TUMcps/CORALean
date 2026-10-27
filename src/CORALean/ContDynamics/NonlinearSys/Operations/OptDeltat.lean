module

public import CORALean.ContDynamics.NonlinearSys.Definitions.OptStep
public import CORALean.ContDynamics.NonlinearSys.Operations.InterpGain
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Real.Basic
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `optDeltat`: the time step size that balances the two wrapping effects

Line 10 of [1, Alg. 2], which is its §5.4, and lines 8 and 12 of [2, Alg. 2],
whose (30) and (31) are eq. (57) and eq. (58): over a finite horizon `h`
walked in `λ = ζ_δ^{-λ'}` steps, (57) estimates the size the start set reaches
and (58) minimizes it over `λ'`. Too large a step makes the set of abstraction
errors large, too small a step reduces too often; the minimum is the balance.

`λ` is the lambda binder, so eq. (57)'s `λ` is `lam` and its `λ'` is
`scalings`. `λ'_*` comes back beside `Δt*`: line 16's `estimateGain` needs it.

## Inputs
* `le` – comparison of reals
* `ζδ` – limit gain
* `ζZ` – start-set constant
* `ζA` – matrix constant
* `φ1` – gain at the horizon
* `r₀` – initial radius
* `rabs` – abstraction radius
* `h` – finite horizon
* `fuel` – bound for the search

## Output
* the optimal step size and its scaling index

## References

* [1] [M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive Reachability Algorithms
      for Nonlinear Systems Using Abstraction Error Analysis". Nonlinear Analysis: Hybrid Systems,
      2022.](../../../../../references/2022/wetzlinger-nahs-abstraction-error.md)
* [2] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for Reachability
      Analysis of Nonlinear Systems". Proceedings of the 24th International Conference on Hybrid
      Systems: Computation and Control,
      2021.](../../../../../references/2021/wetzlinger-hscc-adaptive-tuning-nonlinear.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- Increase `λ'` while the estimate keeps falling, and stop at the first
increase — [1]'s own evaluation of eq. (58). -/
@[step_of optDeltat]
noncomputable def step_optDeltatSearch (le : ℝ → ℝ → Bool) (cost : ℕ → ℝ) : ℕ → ℕ → ℕ
  | s, 0 => s
  | s, k + 1 => if le (cost (s + 1)) (cost s) then step_optDeltatSearch le cost (s + 1) k else s

/-- Eq. (57): the size `R(t)` is estimated to reach after the finite horizon,
walked in `λ = ζ_δ^{-λ'}` steps. -/
@[step_of optDeltat]
noncomputable def step_reachSizeEstimate (ζδ ζZ ζA φ1 r₀ rabs : ℝ) (scalings : ℕ) : ℝ :=
  let lam := (1 / ζδ) ^ scalings                                -- λ = ζ_δ^{-λ'}
  let N := ⌊lam⌋₊                                               -- ⌊λ⌋ whole steps
  let b := lam - (N : ℝ)                                        -- the last incomplete step
  let ζAZ := (∑ j ∈ Finset.Icc 1 N,                             -- 53. ζ_{A,Z}(λ)
      (1 + 2 * ζZ) ^ (b + (j : ℝ)) * ζA ^ ((b + (j : ℝ) - 1) / lam))
    + b * (1 + 2 * ζZ) ^ b
  r₀ * (1 + 2 * ζZ) ^ lam * ζA                                  -- 57. the start set, propagated
    + rabs / lam * ζAZ * ∏ j ∈ Finset.range scalings, interpGain ζδ φ1 j -- 57. errors, accumulated


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2] line 10: eq. (58)'s optimal time step size, and the `λ'` it was
found at. -/
noncomputable def optDeltat (le : ℝ → ℝ → Bool) (ζδ ζZ ζA φ1 r₀ rabs h : ℝ) (fuel : ℕ) :
    NonlinearSys.OptStep ℝ :=
  -- 10. eq. (57): the cost function
  let cost := step_reachSizeEstimate ζδ ζZ ζA φ1 r₀ rabs
  -- 10. eq. (58): the argmin over λ'
  let sstar := step_optDeltatSearch le cost 0 fuel
  -- 10. eq. (58): Δt* = h ζ_δ^{λ'}
  ⟨h * ζδ ^ sstar, sstar⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
