module

public import CORALean.ContDynamics.NeurNetContrSysDT.Operations.Map

@[expose] public section

/-!
# At a linear plant, an orbit of `map` is a run

The converse of `Trajectory.linear`: a sequence that starts in `R₀` and steps by `map` is a
`Trajectory` of the closed loop under no disturbance, wherever `W` admits `0`, its noise `0` and
its output what the output equation makes it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- An orbit of `map` from a point of `R₀` is a run, under the zero disturbance. -/
theorem NeurNetContrSysDT.trajectory_of_map {sys : NeurNetContrSysDT (LinearSysDT 𝕋 n) S n}
    {π : Vec ℝ n → Vec ℝ sys.plant.m} {R₀ : S n} {W : Set (Vec ℝ sys.plant.r)} (hW : 0 ∈ W)
    {x : ℕ → Vec ℝ n} (h0 : x 0 ∈ construct R₀) (hstep : ∀ k, x (k + 1) = sys.map π (x k)) :
    sys.Trajectory π R₀ W x 0 := by -- --- PROOF ---
  exact (⟨0, fun k => toRealMat sys.plant.C *ᵥ x k + toRealMat sys.plant.D *ᵥ π (x k) +
      toRealVec sys.plant.k + toRealMat sys.plant.F *ᵥ (0 : Vec ℝ sys.plant.s),
    { init := h0
      input := fun _ => Set.mem_univ _
      dist := fun _ => hW
      noise := fun _ => Set.mem_univ _
      -- `map` is the plant's step with its disturbance term `E 0 = 0`
      step := fun k => by
        rw [hstep k]
        simp [NeurNetContrSysDT.map]
      output := fun _ => rfl }⟩ : ∃ v y, LinearSysDT.Trajectory (S := 𝒮)
        sys.plant (construct R₀) Set.univ W Set.univ x (fun k => π (x k)) 0 v y)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
