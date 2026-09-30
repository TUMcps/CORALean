import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter
import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Reach
import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Simulate
import CORALean.NN.Theorems.EncloseOuter

/-!
# `NeurNetContrSysDT.reach` contains every closed-loop run

Where the two halves of this repository meet, and the meeting is two lines: the
controller's enclosure of the input it produces at the reached state, handed to
the plant's one-step enclosure. Nothing else appears, and nothing new is proved
here — `NeuralNetwork.Sound.enclose_outer` and `LinearSysDT.reach_one_outer` are
both already stated against the interfaces, so neither knows it is being
composed.

The induction hypothesis is used twice, once for each half, and that is the
whole reason the enclosure is loose: the state it places in the reachable set
and the state the controller is read at are the same state in the proof and
independent points in the set.

Reach for `reachSet_subset_reach` for the same guarantee restated on the
reachable set rather than on one run.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.reach_outer (sys : NeurNetContrSysDT 𝕋 S n) {o : ℕ} (ho : 0 < o)
    (R₀ : S n) {π : Vec ℝ n → Vec ℝ n} (hπ : sys.contr.Sound π)
    {x : ℕ → Vec ℝ n} (traj : sys.Trajectory π R₀ x) (k : ℕ) :
    x k ∈ construct (sys.reach o ho R₀ k) := by -- --- PROOF ---
  induction k with
  | zero => exact traj.init
  | succ k ih =>
    show x (k + 1) ∈ construct (sys.plant.reach
      ⟨sys.reach o ho R₀ k, sys.contr.enclose (sys.reach o ho R₀ k), 0, 1⟩ ⟨o, ho⟩)
    rw [traj.step k]
    exact sys.plant.reach_one_outer ho _ _ ih (hπ.enclose_outer _ _ ih)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
