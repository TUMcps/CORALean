module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalInputTermFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TaylorCoeffBoundsFloat
public import CORALean.ContSet.Interval.Float.Theorems.MatPowOuter
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter

@[expose] public section

/-!
# Every member's input term lies in the float box

`matPow_outer` puts `Mⁱ` in the power box, `taylorCoeffBounds_mem` the scalar
in its interval, and `smul_outer` joins them: the float counterpart of the point
term `LinearSys.inputTerm` needs nothing more.

## Inputs
* `A` – float interval matrix
* `r` – float step length
* `M` – member matrix
* `i` – order index

## Hypotheses
* `hr` – step length nonnegative
* `hM` – member lies in the interval matrix

## Conclusion
* the member's input term lies in the float box
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.smul_pow_mem_intervalInputTerm (A : Interval (Mat 𝕋 n n)) {r : 𝕋}
    (hr : 0 ≤ toReal r) {M : Mat ℝ n n} (hM : M ∈ A.construct) (i : ℕ) :
    (toReal r ^ (i + 1) / (Nat.factorial (i + 1) : ℝ)) • M ^ i
      ∈ (MatExp.intervalInputTerm A r i).construct := by
  obtain ⟨hlo, hhi⟩ := MatExp.taylorCoeffBounds_mem hr (i + 1)
  rw [MatExp.intervalInputTerm, Interval.materialiseMat_eq]
  exact Interval.smul_outer hlo hhi _ (Interval.matPow_outer A hM i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
