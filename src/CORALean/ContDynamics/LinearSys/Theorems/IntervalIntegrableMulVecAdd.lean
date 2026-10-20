module

public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# The flow integrand is interval integrable

`A x + u`, and with it `A x + u + w`: the state part is continuous over a
compact window, the signal part integrable by hypothesis, so their sum
integrates. Every subtraction of one flow equation from another goes through
this — `intervalIntegral.integral_sub` and `integral_add` both want each side
integrable first — so it is stated once rather than rebuilt in each file.

The window `[0, τ]` is any sub-window of `[0, t]`, which is what lets a flow
equation stated for all `τ ∈ [0, t]` be manipulated at each `τ` separately.

## Inputs
* `A` – matrix
* `f` – continuous function
* `v` – integrable function
* `t` – window end
* `τ` – integration limit

## Hypotheses
* `hf` – function continuous on the window
* `hv` – second function integrable on the window
* `ht` – window end nonnegative
* `hτ` – integration limit within the window

## Conclusion
* the flow integrand is interval integrable
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar MeasureTheory

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `ρ ↦ A *ᵥ f ρ + v ρ` integrates over `[0, τ]` whenever `f` is continuous on
the enclosing window and `v` is integrable over it. -/
theorem intervalIntegrable_mulVec_add (A : Mat ℝ n n) {f v : ℝ → Vec ℝ n} {t τ : ℝ}
    (hf : ContinuousOn f (Set.Icc 0 t)) (hv : IntervalIntegrable v volume 0 t)
    (ht : 0 ≤ t) (hτ : τ ∈ Set.Icc (0:ℝ) t) :
    IntervalIntegrable (fun ρ => A *ᵥ f ρ + v ρ) volume 0 τ := by -- --- PROOF ---
  have hAf : IntervalIntegrable (fun ρ => A *ᵥ f ρ) volume 0 τ := by
    have hc : ContinuousOn (fun ρ => A *ᵥ f ρ) (Set.Icc 0 τ) :=
      (mulVecL A).continuous.comp_continuousOn (hf.mono (Set.Icc_subset_Icc_right hτ.2))
    rw [← Set.uIcc_of_le hτ.1] at hc
    exact hc.intervalIntegrable
  -- the signal's own window shrinks to `[0, τ]`
  exact hAf.add (hv.mono_set (by
    rw [Set.uIcc_of_le hτ.1, Set.uIcc_of_le ht]; exact Set.Icc_subset_Icc_right hτ.2))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
