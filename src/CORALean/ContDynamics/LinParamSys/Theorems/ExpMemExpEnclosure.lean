import CORALean.ContDynamics.LinParamSys.Operations.ExpEnclosure
import CORALean.ContDynamics.LinParamSys.Theorems.ReachOrderAdmissible
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntervalEnclosure
import CORALean.ContSet.Interval.Real.Theorems.SmulOuter

/-!
# Every member's exponential lies in `expEnclosure`

`exp_mem_expIntervalEnclosure` at the member `t • A` of the box `t • sys.A`,
its order condition met by the raise `expEnclosure` makes: a larger order only
shrinks `‖(t • sys.A).absMax‖ / (η + 2)`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `e^{A t}` is in `expEnclosure t η` at every member `A` of `sys.A`, every `t`
and every requested order. -/
theorem LinParamSys.exp_mem_expEnclosure (sys : LinParamSys ℐ n) (t : ℝ) (η : ℕ)
    {A : Mat ℝ n n} (hA : A ∈ construct sys.A) :
    exp (t • A) ∈ construct (sys.expEnclosure t η) := by -- --- PROOF ---
  -- the raised order is at least the admissible one, so its denominator is larger
  have hadm := sys.reachOrder_admissible t
  have hle : (((sys.reachOrder t + 2 : ℕ) : ℝ) + 2)
      ≤ ((max η (sys.reachOrder t + 2) : ℕ) : ℝ) + 2 := by
    have : sys.reachOrder t + 2 ≤ max η (sys.reachOrder t + 2) := le_max_right _ _
    exact_mod_cast Nat.add_le_add_right this 2
  have hε : ‖(Interval.smul t sys.A).absMax‖
      / (((max η (sys.reachOrder t + 2) : ℕ) : ℝ) + 2) < 1 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hle) hadm
  exact MatExp.exp_mem_expIntervalEnclosure _ _ (Interval.smul_outer t sys.A hA) hε

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
