import CORALean.ContDynamics.LinearARX.API
import CORALean.ContDynamics.LinearSysDT.Instances
import CORALean.ContSet.Interval.Real.Instances

/-!
# An order-2 scalar ARX model, bounded by conversion

`y(k) = y(k-1) - y(k-2) + u(k) + u(k-1)`, one output and
one input, so the converted system has two states. The all-zero signal is a
trajectory for any initial box and input box containing `0`, and `reach_outer`
places its window in the reachable set of the conversion at every step.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Ā = (1, -1)`, `B̄ = (1, 1, 0)`. -/
def Example.arx : LinearARX ℝ 1 1 2 where
  Abar i := Matrix.of fun _ _ => if i.val = 0 then 1 else -1
  Bbar j := Matrix.of fun _ _ => if j.val = 2 then 0 else 1

/-- The zero signal is a run for any boxes containing the origin. -/
theorem Example.arx_zero_trajectory (Y₀ : Interval (Vec ℝ 2)) (U : Interval (Vec ℝ 1))
    (hY : (0 : Vec ℝ 2) ∈ construct Y₀) (hU : (0 : Vec ℝ 1) ∈ construct U) :
    Example.arx.Trajectory (S := fun n => Interval (Vec ℝ n)) Y₀ U (fun _ => 0) (fun _ => 0)
    where
  init := hY
  input _ := hU
  step k _ := by simp

/-- Hence the window of outputs at step `k` is in the converted system's reach. -/
example (Y₀ : Interval (Vec ℝ 2)) (U : Interval (Vec ℝ 1)) (hY : (0 : Vec ℝ 2) ∈ construct Y₀)
    (hU : (0 : Vec ℝ 1) ∈ construct U) {o : ℕ} (ho : 0 < o) (k : ℕ) :
    LinearARX.stack 2 (fun _ => (0 : Vec ℝ 1)) k ∈ construct
      (Example.arx.toLinearSysDT.reach (S := fun n => Interval (Vec ℝ n))
        ⟨Y₀, Example.arx.inputSet (S := fun n => Interval (Vec ℝ n)) U, 0, k⟩ ⟨o, ho⟩) :=
  Example.arx.reach_outer (S := fun n => Interval (Vec ℝ n)) ho Y₀ U
    (Example.arx_zero_trajectory Y₀ U hY hU) k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
