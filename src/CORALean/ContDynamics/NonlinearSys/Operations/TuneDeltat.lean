module

public import CORALean.ContDynamics.NonlinearSys.Operations.EstimateGain
public import CORALean.ContDynamics.NonlinearSys.Operations.OptDeltat
public import CORALean.ContDynamics.NonlinearSys.Operations.TuneDeltatInit

@[expose] public section

/-!
# `Alg. 2`: tuning of the time step size Δt

[1, Alg. 2], which is its §3.4. Both branches end in eq. (31)'s `Δt* = Δ ζ_δ^{k'_*}`,
`optDeltat`; what differs is where the finite horizon `Δ` comes from. From the second step on
(lines 10-13) it is the last step's `Δ` rescaled by the gain; in the first (lines 2-8) `Δ` is
shrunk by `ζ_δ` until eq. (32)'s `φ₁ ≥ ζ_Δ` holds — `tuneDeltatInit`. Scalars throughout, as
`optDeltat` is: `dabs` and `rabs` are the caller's. [2, Alg. 2]'s line 1 is line 10 here;
(27), (29), (30), (31) are [2]'s (54), (56), (57), (58).

## Inputs
* `le` – comparison of reals
* `dabs` – box diameter of the abstraction error
* `rabs` – radius of the abstraction error
* `ζδ` – limit gain
* `ζΔ` – gain threshold
* `ζZ` – start-set constant
* `ζP` – second constant
* `r₀` – initial radius
* `φ1` – last step's gain
* `Δ` – last finite horizon
* `Δinit` – initial finite horizon
* `s` – step number
* `fuel` – bound for the search

## Output
* the step size and the gain for the next step, or none

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for
      Reachability Analysis of Nonlinear Systems". HSCC, 2021, Article 16.
* [2] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 2]: the optimal time step size `Δt*` and the gain `φ₁` to hand the
next step, and `none` where the first step's search for `Δ` gave out. -/
noncomputable def tuneDeltat (le : ℝ → ℝ → Bool) (dabs : ℝ → Fin n → ℝ) (rabs : ℝ → ℝ)
    (ζδ ζΔ ζZ ζP r₀ φ1 Δ Δinit : ℝ) (s fuel : ℕ) : Option (NonlinearSys.TunedStep ℝ) :=
  -- 1. if s = 1 then
  if s = 1 then
    -- 2. initialize Δt
    let Δ₀ := Δinit
    -- 3.-7. the loop of (32)
    match tuneDeltatInit le dabs ζδ ζΔ Δ₀ fuel with
    | none => none
    | some ⟨Δ₁, φ₁⟩ =>
      -- 8. Δt* by (31)
      let opt := optDeltat le ζδ ζZ ζP φ₁ r₀ (rabs Δ₁) Δ₁ fuel
      some ⟨opt.Δt, φ₁⟩
  -- 9. else
  else
    -- 10. Δ ← Δ(ζ_δ-ζ_Δ)/(ζ_δ-φ₁)
    let Δk := Δ * (ζδ - ζΔ) / (ζδ - φ1)
    -- 11. R_abs(Δ), and r_abs,1
    let rabs1 := rabs Δk
    -- 12. Δt* by (31)
    let opt := optDeltat le ζδ ζZ ζP φ1 r₀ rabs1 Δk fuel
    -- 13. (29)'s r_abs,k, at Δt*
    let rabsk := rabs opt.Δt
    -- 13. φ₁ by (29)
    let φ₁ := estimateGain le ζδ ((1 / ζδ) ^ opt.exponent)
      rabs1 rabsk opt.exponent fuel
    some ⟨opt.Δt, φ₁⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
