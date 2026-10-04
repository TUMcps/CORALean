import CORALean.Global.BlockDiag
import CORALean.ContSet.ConZonotope.Real.ConZonotope
import CORALean.ContSet.Conversion.Real.HPolytope_to_SpectraShadow
import CORALean.ContSet.Conversion.Real.Zonotope_to_SpectraShadow

/-!
# A constrained zonotope as a spectrahedral shadow

Exact. CORA's `@conZonotope/spectraShadow` lays the box inequalities `1 ± βⱼ ≥ 0` and one
block per constraint row `b - Aβ ≥ 0`, `Aβ - b ≥ 0` along one block-diagonal matrix. Here the
constraints are the polytope `P` on the coefficient space, so the second half is the diagonal
LMI of `HPolytope.spectraShadow` at `P`, and the box half is the zonotope's own. A
block-diagonal matrix is positive semidefinite exactly when both blocks are.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {α : Type} [AddCommGroup α] [Module ℝ α]

def ConZonotope.spectraShadow (cZ : ConZonotope α) : SpectraShadow α where
  k := (cZ.h + cZ.h) + (cZ.P.m + cZ.P.me + cZ.P.me)
  m := cZ.h
  A₀ := blockDiag 0 (Zonotope.spectraShadow ⟨cZ.h, cZ.c, cZ.G⟩).A₀ cZ.P.spectraShadow.A₀
  A := fun j => blockDiag 0 ((Zonotope.spectraShadow ⟨cZ.h, cZ.c, cZ.G⟩).A j)
    (cZ.P.spectraShadow.A j)
  c := cZ.c
  G := cZ.G


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [AddCommGroup α] in
/-- The inequality holds when both blocks' do: the box and the polytope. -/
theorem ConZonotope.aux_posSemidef_spectraShadow_iff (cZ : ConZonotope α) (β : Fin cZ.h → ℝ) :
    (cZ.spectraShadow.A₀ + ∑ j, β j • cZ.spectraShadow.A j).PosSemidef
      ↔ (∀ j, |β j| ≤ 1) ∧ β ∈ cZ.P.construct := by -- --- PROOF ---
  change (blockDiag 0 (Zonotope.spectraShadow ⟨cZ.h, cZ.c, cZ.G⟩).A₀ cZ.P.spectraShadow.A₀
      + ∑ j, β j • blockDiag 0 ((Zonotope.spectraShadow ⟨cZ.h, cZ.c, cZ.G⟩).A j)
        (cZ.P.spectraShadow.A j)).PosSemidef ↔ _
  simp only [← blockDiag_smul]
  rw [← blockDiag_sum, ← blockDiag_add, posSemidef_blockDiag_iff]
  exact and_congr (Zonotope.posSemidef_spectraShadow_iff ⟨cZ.h, cZ.c, cZ.G⟩ β)
    (HPolytope.posSemidef_spectraShadow_iff cZ.P β)


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.spectraShadow_exact (cZ : ConZonotope α) :
    cZ.construct = cZ.spectraShadow.construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨β, hβ, hP, rfl⟩
    exact ⟨β, (ConZonotope.aux_posSemidef_spectraShadow_iff cZ β).mpr ⟨hβ, hP⟩, rfl⟩
  · rintro _ ⟨β, hβ, rfl⟩
    obtain ⟨h₁, h₂⟩ := (ConZonotope.aux_posSemidef_spectraShadow_iff cZ β).mp hβ
    exact ⟨β, h₁, h₂, rfl⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
