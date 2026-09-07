import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter
import CORALean.ContDynamics.NeurNetContrSysDT.Operations
import CORALean.NN.Theorems.EncloseOuter

/-!
# `NeurNetContrSysDT.reach` contains every closed-loop run

Where the two halves of this repository meet, and the meeting is two lines: the
controller's enclosure of the input it produces at the reached state, handed to
the plant's one-step enclosure. Nothing else appears, and nothing new is proved
here — `NeuralNetwork.enclose_outer` and `LinearSysDT.reach_one_outer` are
both already stated against the interfaces, so neither knows it is being
composed.

The induction hypothesis is used twice, once for each half, and that is the
whole reason the enclosure is loose: the state it places in the reachable set
and the state the controller is read at are the same state in the proof and
independent points in the set.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.reach_outer (sys : NeurNetContrSysDT 𝕋 S n) (o : ℕ) (R₀ : S n)
    {x : ℕ → Vec ℝ n} (traj : sys.Trajectory R₀ x) (k : ℕ) :
    x k ∈ construct (sys.reach o R₀ k) := by -- --- PROOF ---
  induction k with
  | zero => exact traj.init
  | succ k ih =>
    show x (k + 1) ∈ construct (sys.plant.reach o (sys.reach o R₀ k)
      (sys.contr.enclose (sys.reach o R₀ k)) 1)
    rw [traj.step k]
    exact sys.plant.reach_one_outer o _ _ ih (sys.contr.enclose_outer _ _ ih)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
