import CORALean.ContDynamics.LinearARX.LinearARX
import CORALean.ContDynamics.LinearARX.Operations.ToLinearSysDT
import CORALean.ContDynamics.LinearARX.Theorems.ReachOuter
import CORALean.ContDynamics.LinearSysDT.Instances
import CORALean.ContSet.Interval.Real.Instances

/-!
# An order-2 scalar ARX model, bounded by conversion

`y(k) = y(k-1) - y(k-2) + u(k) + u(k-1)`, one output and
one input, so the converted system has two states. Under the constant input
`u ≡ 1` the model has the steady state `y ≡ 2` (`2 = 2 - 2 + 1 + 1`), a trajectory for any
initial box containing `(2, 2)` and input box containing `1`, and `reach_outer`
places its window in the reachable set of the conversion at every step.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Ā = (1, -1)`, `B̄ = (1, 1, 0)`. -/
def Example.arx : LinearARX ℝ 1 1 2 where
  Abar i := Matrix.of fun _ _ => if i.val = 0 then 1 else -1
  Bbar j := Matrix.of fun _ _ => if j.val = 2 then 0 else 1
  dt := 1

/-- The steady state `y ≡ 2` under `u ≡ 1` is a run for any boxes containing `(2, 2)` and `1`. -/
theorem Example.arx_steady_isTrajectory (Y₀ : Interval (Vec ℝ 2)) (U : Interval (Vec ℝ 1))
    (hY : ![(2 : ℝ), 2] ∈ construct Y₀) (hU : (![1] : Vec ℝ 1) ∈ construct U) :
    Example.arx.IsTrajectory (S := ℐ𝒱) Y₀ U (fun _ => ![2]) (fun _ => ![1])
    where
  init := by
    convert hY using 1
    funext r
    fin_cases r <;> simp [LinearARX.stack]
  input _ := hU
  step k _ := by
    ext i
    fin_cases i
    simp [Example.arx, Fin.sum_univ_succ]
    norm_num

/-- Hence the window of outputs at step `k` is in the converted system's reach. -/
example (Y₀ : Interval (Vec ℝ 2)) (U : Interval (Vec ℝ 1)) (hY : ![(2 : ℝ), 2] ∈ construct Y₀)
    (hU : (![1] : Vec ℝ 1) ∈ construct U) {o : ℕ} (ho : 0 < o) (k : ℕ) :
    LinearARX.stack 2 (fun _ => (![2] : Vec ℝ 1)) k ∈ construct
      (Example.arx.toLinearSysDT.reach (S := ℐ𝒱)
        ⟨Y₀, Example.arx.inputSet (S := ℐ𝒱) U, 0, k⟩ ⟨o, ho⟩) :=
  Example.arx.reach_outer (S := ℐ𝒱) ho Y₀ U
    (Example.arx_steady_isTrajectory Y₀ U hY hU) k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
