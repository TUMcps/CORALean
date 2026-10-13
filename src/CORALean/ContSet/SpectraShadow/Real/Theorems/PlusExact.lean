module

public import CORALean.ContSet.SpectraShadow.Real.Theorems.PosSemidefPlusIff

@[expose] public section

/-!
# `SpectraShadow.plus` is exactly the Minkowski sum

Both inequalities hold exactly when the block-diagonal one does, by
`posSemidef_blockDiag_iff`, and a variable of one set sees a zero block in the
other's rows, so the two sets' variables stay independent: `Fin.append β₁ β₂`
is the witness one way and the two halves of `β` the other. Nothing is lost, which
is what `Plus` gives up in every other representation here and the reason this one
exists as a sum's target.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- `Fin.sum_univ_add` at `plus`'s variable count, stated through the projection
because that is the form the goal has and simp will not rewrite a binder's type. -/
theorem SpectraShadow.aux_sum_univ_plus {S₁ S₂ : SpectraShadow α} {M : Type}
    [AddCommMonoid M] (f : Fin (S₁.m + S₂.m) → M) :
    ∑ j : Fin (S₁.plus S₂).m, f j
      = ∑ j, f (Fin.castAdd S₂.m j) + ∑ j, f (Fin.natAdd S₁.m j) :=
  Fin.sum_univ_add f

/-- The same for the generators. -/
theorem SpectraShadow.aux_gen_plus (S₁ S₂ : SpectraShadow α) (β : Fin (S₁.m + S₂.m) → ℝ) :
    (S₁.plus S₂).c + ∑ i : Fin (S₁.plus S₂).m, β i • (S₁.plus S₂).G i
      = (S₁.c + ∑ i, β (Fin.castAdd S₂.m i) • S₁.G i)
          + (S₂.c + ∑ j, β (Fin.natAdd S₁.m j) • S₂.G j) := by
  rw [SpectraShadow.aux_sum_univ_plus]
  simp only [SpectraShadow.plus, Fin.append_left, Fin.append_right]
  abel


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.plus_exact (S₁ S₂ : SpectraShadow α) :
    S₁.construct + S₂.construct = (S₁.plus S₂).construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨x₁, ⟨β₁, h₁, rfl⟩, x₂, ⟨β₂, h₂, rfl⟩, rfl⟩
    refine ⟨Fin.append β₁ β₂, ?_, ?_⟩
    · rw [SpectraShadow.posSemidef_plus_iff]
      simpa using ⟨h₁, h₂⟩
    · rw [SpectraShadow.aux_gen_plus]
      simp
  · rintro _ ⟨β, hβ, rfl⟩
    rw [SpectraShadow.posSemidef_plus_iff] at hβ
    exact ⟨_, ⟨_, hβ.1, rfl⟩, _, ⟨_, hβ.2, rfl⟩, (SpectraShadow.aux_gen_plus S₁ S₂ β).symm⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
