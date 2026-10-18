module

public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.OutputSet
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachOuter
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.MulVecJoinInput
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ToRealMatLeftCols
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ToRealMatRightCols
public import CORALean.ContDynamics.OutputEq.Theorems.OutputSetOuter
public import CORALean.ContDynamics.LinearSysDT.Operations.Basic

@[expose] public section

/-!
# The output of a closed-loop run lies in the output set of its reachable set

`LinearSysDT.output_outer`'s statement, with the controller's own enclosure of
its input and the external inputs `U_ext` standing in for a free `U`: `reach_outer` places the
state, `NeuralNetwork.Sound.enclose_outer` at that same enclosure places the network's part of the
input the controller produces there, and the external part is in `U_ext`; `D [a; e]` splits as
`D_nn a + D_ext e` (`outputSet`), each in its own product. The input set the output is read at is
the enclosed one, not the looser one `reach` itself widens through, as
`NeurNetContrSysDT.Operations` already notes at the state.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar Plus Reduce Mtimes

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
    [OfScalarPoint 𝕋 S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NeurNetContrSysDT.output_outer (sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n)
    (U_ext : S sys.nExt) {o : ℕ} (ho : 0 < o) (R₀ : S n) {π : Vec ℝ n → Vec ℝ sys.m}
    (hπ : sys.contr.Sound π) {W : Set (Vec ℝ sys.plant.r)}
    (hW : ∀ v ∈ W, toRealMat sys.plant.E *ᵥ v = 0) {x : ℕ → Vec ℝ n} {v : ℕ → Vec ℝ sys.nExt}
    {w : ℕ → Vec ℝ sys.plant.r} (traj : sys.IsTrajectory π R₀ (construct U_ext) W x v w)
    (k : ℕ) : -- --- STMT ---
    sys.plant.outputEq.eval (x k) (sys.input (π (x k)) (v k)) ∈ construct
      (sys.outputSet U_ext (sys.reach U_ext ⟨R₀, 0, k⟩ ⟨o, ho⟩)) := by -- --- PROOF ---
  have hx := sys.reach_outer U_ext ho R₀ hπ hW traj k
  have hv := (traj.linear hW).2.1 k
  unfold OutputEq.eval NeurNetContrSysDT.input
  rw [mulVec_joinInput, ← toRealMat_leftCols, ← toRealMat_rightCols]
  exact plus_outer _ _ (Set.add_mem_add (plus_outer _ _ (Set.add_mem_add
    (mtimes_outer _ _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx)))
    (plus_outer _ _ (Set.add_mem_add
      (mtimes_outer _ _ (Set.mem_biUnion rfl
        (Set.mem_image_of_mem _ (hπ.enclose_outer _ _ hx))))
      (mtimes_outer _ _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hv)))))))
    (OfScalarPoint.mem_ofVec _))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
