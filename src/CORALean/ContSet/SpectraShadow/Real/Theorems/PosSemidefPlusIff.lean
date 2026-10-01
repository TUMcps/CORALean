import CORALean.ContSet.SpectraShadow.Real.Theorems.LmiAppend

/-!
# The inequality of a sum holds exactly when both do

`posSemidef_blockDiag_iff` after `lmi_append`: the combination is block diagonal,
so it is positive semidefinite exactly when each block is, and each block is one
set's inequality at its own half of the variables.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
theorem SpectraShadow.posSemidef_plus_iff (S₁ S₂ : SpectraShadow α)
    (β : Fin (S₁.m + S₂.m) → ℝ) :
    ((S₁.plus S₂).A₀ + ∑ i : Fin (S₁.plus S₂).m, β i • (S₁.plus S₂).A i).PosSemidef
      ↔ (S₁.A₀ + ∑ i, β (Fin.castAdd S₂.m i) • S₁.A i).PosSemidef
        ∧ (S₂.A₀ + ∑ j, β (Fin.natAdd S₁.m j) • S₂.A j).PosSemidef := by
  rw [← posSemidef_blockDiag_iff, ← SpectraShadow.lmi_append]
  exact Iff.rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
