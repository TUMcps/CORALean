module

public import CORALean.Global.BlockDiag
public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# A zonotope as a spectrahedral shadow

Exact. The unit box `|βⱼ| ≤ 1` is the diagonal inequality `1 + βⱼ ≥ 0`, `1 - βⱼ ≥ 0`
for every `j`, so the matrix has `h` entries of each kind, `2h` in all, laid along
the diagonal of one block-diagonal matrix: `1 + βⱼ` in the first `h` rows and
`1 - βⱼ` in the last `h`. A diagonal matrix is positive semidefinite exactly when
its entries are nonnegative, so the inequality holds exactly on the cube, and the
centre and generators are the zonotope's own.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def Zonotope.spectraShadow (Z : Zonotope α) : SpectraShadow α where
  k := Z.h + Z.h
  m := Z.h
  A₀ := blockDiag 0 1 1
  A := fun j => blockDiag 0 (diagonal (Pi.single j 1)) (diagonal (Pi.single j (-1)))
  c := Z.c
  G := Z.G


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The inequality, entry by entry: `1 + βⱼ` on the first block and `1 - βⱼ` on the
second. Stated at plain dimensions, so every index is a sum and `simp` reads it. -/
theorem Zonotope.aux_lmi_spectraShadow {h : ℕ} (β : Fin h → ℝ) :
    blockDiag 0 (1 : Mat ℝ h h) 1 + ∑ j, β j • blockDiag 0 (diagonal (Pi.single j 1))
        (diagonal (Pi.single j (-1) : Fin h → ℝ))
      = blockDiag 0 (diagonal fun i => 1 + β i) (diagonal fun i => 1 - β i) := by -- --- PROOF ---
  refine blockDiag_ext ?_ ?_ ?_ ?_ <;> intros <;>
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      blockDiag_castAdd_castAdd, blockDiag_castAdd_natAdd, blockDiag_natAdd_castAdd,
      blockDiag_natAdd_natAdd] <;>
    simp [diagonal_apply, Pi.single_apply, Matrix.one_apply]
  all_goals (split_ifs <;> ring)


-- =======================================  MAIN THEOREM  ======================================= --

omit [AddCommGroup α] [Module ℝ α] in
/-- The cube is where both diagonals are nonnegative. -/
theorem Zonotope.posSemidef_spectraShadow_iff (Z : Zonotope α) (β : Fin Z.h → ℝ) :
    (Z.spectraShadow.A₀ + ∑ j, β j • Z.spectraShadow.A j).PosSemidef
      ↔ ∀ j, |β j| ≤ 1 := by -- --- PROOF ---
  change (blockDiag 0 (1 : Mat ℝ Z.h Z.h) 1 + ∑ j, β j • blockDiag 0 (diagonal (Pi.single j 1))
    (diagonal (Pi.single j (-1) : Fin Z.h → ℝ))).PosSemidef ↔ _
  rw [Zonotope.aux_lmi_spectraShadow, posSemidef_blockDiag_iff, posSemidef_diagonal_iff,
    posSemidef_diagonal_iff]
  constructor
  · rintro ⟨h₁, h₂⟩ j
    exact abs_le.mpr ⟨by linarith [h₁ j], by linarith [h₂ j]⟩
  · intro h
    exact ⟨fun i => by linarith [(abs_le.mp (h i)).1], fun i => by linarith [(abs_le.mp (h i)).2]⟩

theorem Zonotope.spectraShadow_exact (Z : Zonotope α) :
    Z.construct = Z.spectraShadow.construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨β, hβ, rfl⟩
    exact ⟨β, (Zonotope.posSemidef_spectraShadow_iff Z β).mpr hβ, rfl⟩
  · rintro _ ⟨β, hβ, rfl⟩
    exact ⟨β, (Zonotope.posSemidef_spectraShadow_iff Z β).mp hβ, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
