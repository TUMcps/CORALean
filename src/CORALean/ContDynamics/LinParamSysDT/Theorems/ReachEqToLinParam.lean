import CORALean.ContDynamics.LinParamSysDT.Operations.Reach
import CORALean.ContDynamics.LinParamSysDT.Operations.Simulate
import CORALean.ContDynamics.LinearSysDT.Operations.Reach
import CORALean.ContDynamics.LinearSysDT.Operations.ReachOrders
import CORALean.ContDynamics.LinearSysDT.Operations.ReachHeld
import CORALean.ContDynamics.LinearSysDT.Operations.Simulate
import CORALean.ContDynamics.LinParamSysDT.Theorems.ToLinParam

/-!
# `toLinParam`'s reach is `LinearSysDT`'s

The two recursions are the same term at every step: both read off `sys.A`
through the same `mtimes`, and `toLinParam` changes nothing `mtimes`, `plus`
or `reduce` can see.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.reach_eq_toLinParam (sys : LinearSysDT 𝕋 n) {o : ℕ} (ho : 0 < o)
    (R₀ U : S n) (k : ℕ) :
    sys.toLinParam.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ =
      sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩ := by -- --- PROOF ---
  induction k with
  | zero => rfl
  | succ k ih =>
    show reduce (plus (mtimes sys.toLinParam.A (sys.toLinParam.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)) U) o =
      reduce (plus (mtimes sys.A (sys.reach ⟨R₀, U, 0, k⟩ ⟨o, ho⟩)) U) o
    rw [ih]
    rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
