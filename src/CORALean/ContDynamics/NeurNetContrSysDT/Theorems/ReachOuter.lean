module

public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOneOuter
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Reach
public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Simulate
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.IsTrajectoryLinear
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.MulVecJoinInput
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ToRealMatLeftCols
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ToRealMatRightCols
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

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable [OfScalarPoint 𝕋 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.reach_outer (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n)
    (U_ext : S sys.nExt) {o : ℕ} (ho : 0 < o)
    (R₀ : S n) {π : Vec ℝ n → Vec ℝ sys.m} (hπ : sys.contr.Sound π)
    {W : Set (Vec ℝ sys.plant.r)}
    (hW : ∀ v ∈ W, toRealMat sys.plant.E *ᵥ v = 0) {x : ℕ → Vec ℝ n} {v : ℕ → Vec ℝ sys.nExt}
    {w : ℕ → Vec ℝ sys.plant.r} (traj : sys.IsTrajectory π R₀ (construct U_ext) W x v w) (k : ℕ) :
    x k ∈ construct (sys.reach U_ext ⟨R₀, 0, k⟩ ⟨o, ho⟩) := by -- --- PROOF ---
  obtain ⟨hinit, hv, hstep⟩ := traj.linear hW
  induction k with
  | zero => exact hinit
  | succ k ih =>
    set R := sys.reach U_ext ⟨R₀, 0, k⟩ ⟨o, ho⟩
    show x (k + 1) ∈ construct (sys.plant.reach
      ⟨R, plus (plus (mtimes (leftCols sys.hm sys.plant.B) (sys.contr.enclose R))
        (mtimes (rightCols sys.hm sys.plant.B) U_ext)) (OfScalarPoint.ofVec sys.plant.c), 0, 1⟩
        ⟨o, ho⟩)
    -- the input `B_nn π(x) + B_ext v + c` is in `B_nn N(R) ⊕ B_ext U_ext ⊕ c`
    have hu : toRealMat (leftCols sys.hm sys.plant.B) *ᵥ π (x k) +
        toRealMat (rightCols sys.hm sys.plant.B) *ᵥ v k + toRealVec sys.plant.c ∈
        construct (plus (plus (mtimes (leftCols sys.hm sys.plant.B) (sys.contr.enclose R))
          (mtimes (rightCols sys.hm sys.plant.B) U_ext))
          (OfScalarPoint.ofVec (S := S) sys.plant.c)) :=
      plus_outer _ _ ⟨_, plus_outer _ _ ⟨_, mtimes_outer _ _ (Set.mem_biUnion
        (Set.mem_singleton _) ⟨_, hπ.enclose_outer _ _ ih, rfl⟩), _,
        mtimes_outer _ _ (Set.mem_biUnion (Set.mem_singleton _) ⟨_, hv k, rfl⟩), rfl⟩, _,
        OfScalarPoint.mem_ofVec sys.plant.c, rfl⟩
    rw [hstep k]
    unfold NeurNetContrSysDT.map NeurNetContrSysDT.input
    rw [mulVec_joinInput, ← toRealMat_leftCols, ← toRealMat_rightCols, add_assoc]
    exact sys.plant.reach_one_outer ho _ _ ih hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
