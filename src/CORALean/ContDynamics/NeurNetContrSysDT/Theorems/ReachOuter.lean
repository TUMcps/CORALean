module

public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Reach
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Simulate
public import CORALean.NN.Theorems.EncloseOuter

@[expose] public section

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

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable [OfScalarPoint 𝕋 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.reach_outer (sys : NeurNetContrSysDT 𝕋 S n) {o : ℕ} (ho : 0 < o)
    (R₀ : S n) {π : Vec ℝ n → Vec ℝ sys.plant.m} (hπ : sys.contr.Sound π)
    {x : ℕ → Vec ℝ n} (traj : sys.Trajectory π R₀ x) (k : ℕ) :
    x k ∈ construct (sys.reach ⟨R₀, 0, k⟩ ⟨o, ho⟩) := by -- --- PROOF ---
  induction k with
  | zero => exact traj.init
  | succ k ih =>
    set R := sys.reach ⟨R₀, 0, k⟩ ⟨o, ho⟩
    show x (k + 1) ∈ construct (sys.plant.reach
      ⟨R, plus (mtimes sys.plant.B (sys.contr.enclose R)) (OfScalarPoint.ofVec sys.plant.c), 0, 1⟩
        ⟨o, ho⟩)
    -- the input `B π(x) + c` is in `B N(R) ⊕ c`, the controller's output in `N(R)`
    have hu : toRealMat sys.plant.B *ᵥ π (x k) + toRealVec sys.plant.c ∈
        construct (plus (mtimes sys.plant.B (sys.contr.enclose R))
          (OfScalarPoint.ofVec (S := S) sys.plant.c)) :=
      plus_outer _ _ ⟨_, mtimes_outer sys.plant.B _ (Set.mem_biUnion (Set.mem_singleton _)
        ⟨_, hπ.enclose_outer _ _ ih, rfl⟩), _, OfScalarPoint.mem_ofVec sys.plant.c, rfl⟩
    rw [traj.step k, add_assoc]
    exact sys.plant.reach_one_outer ho _ _ ih hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
