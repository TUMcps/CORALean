module

public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Map
public import CORALean.ContDynamics.NeurNetContrSysDT.NeurNetContrSysDT

@[expose] public section

/-!
# At a linear plant, a sequence stepping by `map` is a run

The converse of `IsTrajectory.linear`: a sequence that starts in `R₀` and steps by `map` under
external inputs in `U_ext` is a `IsTrajectory` of the closed loop under no disturbance, wherever `W`
admits `0`, its noise `0` and its output what the output equation makes it.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A sequence from a point of `R₀` stepping by `map` under external inputs in `U_ext` is a run,
under the zero disturbance. -/
theorem NeurNetContrSysDT.isTrajectory_of_map {sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n}
    {π : Vec ℝ n → Vec ℝ sys.m} {R₀ : S n} {U_ext : Set (Vec ℝ sys.nExt)}
    {W : Set (Vec ℝ sys.plant.r)} (hW : 0 ∈ W) {x : ℕ → Vec ℝ n} {v : ℕ → Vec ℝ sys.nExt}
    (h0 : x 0 ∈ construct R₀) (hv : ∀ k, v k ∈ U_ext)
    (hstep : ∀ k, x (k + 1) = sys.map π (x k) (v k)) : -- --- STMT ---
    sys.IsTrajectory π R₀ U_ext W x v 0 := by -- --- PROOF ---
  exact (⟨0, fun k => toRealMat sys.plant.C *ᵥ x k +
      toRealMat sys.plant.D *ᵥ sys.input (π (x k)) (v k) +
      toRealVec sys.plant.k + toRealMat sys.plant.F *ᵥ (0 : Vec ℝ sys.plant.s),
    { init := h0
      input := fun k => ⟨π (x k), Set.mem_univ _, v k, hv k, rfl⟩
      dist := fun _ => hW
      noise := fun _ => Set.mem_univ _
      -- `map` is the plant's step with its disturbance term `E 0 = 0`
      step := fun k => by
        rw [hstep k]
        simp [NeurNetContrSysDT.map]
      output := fun _ => rfl }⟩ : ∃ vn yn, LinearSysDT.IsTrajectory (S := 𝒮)
        sys.plant (construct R₀) (sys.inputSet Set.univ U_ext) W Set.univ x
        (fun k => sys.input (π (x k)) (v k)) 0 vn yn)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
