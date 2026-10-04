import CORALean.ContDynamics.Conform.Definitions.Conformant
import Mathlib.Tactic.Abel

/-!
# [1, Cor. 1]: one-step residuals in `W` and `V` give conformance for every horizon

A recording of states `x`, inputs `u` and outputs `y`, cut into sequential test cases
[1, Def. 4] — test case `m` starts at sample `m`, from the recorded state `x(m)`. If every
one-step state residual `x(t+1) - A x(t) - B u(t)` lies in `W` (20) and every output
residual `y(t) - C x(t) - D u(t)` in `V` (21), the model is conformant on all of
them, at every horizon `K`: the recording is itself a run of the model, the residuals
its disturbances and its noise. The printed proof inducts on the state deviation
(26) instead; the statement is the same.

(20)'s `x_a⁽ᵐ⁾(1)` is `x(m+1) - (A x(m) + B u(m))` here, the test case's states being
the recording's from sample `m` on, which the proof's use of [1, Def. 4] presupposes.

## References

* [1] S. B. Liu, B. Schürmann and M. Althoff. "Guarantees for Real Robotic Systems:
      Unifying Formal Controller Synthesis and Reachset-Conformant Identification". IEEE
      Transactions on Robotics, 39(5):3776-3790, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Pointwise

variable {n p q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. 1]: (20) and (21) on a recording make the model conformant on
its sequential test cases, at every horizon. -/
theorem Conform.Plant.conformant_of_recording (sys : Conform.Plant n p q) (W : Set (Vec ℝ n))
    (V : Set (Vec ℝ q)) (x : ℕ → Vec ℝ n) (u : ℕ → Vec ℝ p) (y : ℕ → Vec ℝ q)
    (hW : ∀ t, x (t + 1) - (sys.A *ᵥ x t + sys.B *ᵥ u t) ∈ W)
    (hV : ∀ t, y t - sys.C *ᵥ x t - sys.D *ᵥ u t ∈ V) (K : ℕ) :
    sys.Conformant {0} W V
      (fun m => ⟨fun k => y (m + k), fun k => u (m + k), x m⟩) K := by -- --- PROOF ---
  intro m k _
  -- the residuals of the recording are the run's disturbances
  let w : ℕ → Vec ℝ n := fun i => x (m + i + 1) - (sys.A *ᵥ x (m + i) + sys.B *ᵥ u (m + i))
  have hrun : ∀ j, sys.state (x m) (fun k => u (m + k)) w j = x (m + j) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      simp only [Conform.Plant.state, ih, w]
      rw [show m + (j + 1) = m + j + 1 by omega]
      abel
  refine ⟨x m, by simp, w, fun i _ => hW (m + i), y (m + k) - sys.C *ᵥ x (m + k)
    - sys.D *ᵥ u (m + k), hV (m + k), ?_⟩
  simp only [Conform.Plant.output, hrun]
  abel

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
