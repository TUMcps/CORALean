import CORALean.ContSet.HPolytope.Float.Operations.Restrict
import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

/-!
# Membership in a restricted polytope

A point is in `P.restrict keepA keepE` iff it meets the rows the tests keep. The index of a kept
row in the filtered list is the row, and every row of the list is kept.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_restrict_iff {P : HPolytope 𝕋 (Vec 𝕋 n)} {keepA : Fin P.m → Bool}
    {keepE : Fin P.me → Bool} {x : Vec ℝ n} :
    x ∈ (P.restrict keepA keepE).construct ↔
      (∀ i, keepA i = true → (toRealMat P.A *ᵥ x) i ≤ toReal (P.b i))
        ∧ ∀ r, keepE r = true → toReal (P.be.inf r) ≤ (toRealMat P.Ae *ᵥ x) r
          ∧ (toRealMat P.Ae *ᵥ x) r ≤ toReal (P.be.sup r) := by -- --- PROOF ---
  rw [HPolytope.mem_construct_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun r hr => ?_⟩
    · -- the kept row is in the list, at some index
      obtain ⟨k, hk⟩ := List.mem_iff_get.mp (List.mem_filter.mpr ⟨List.mem_finRange i, hi⟩)
      have := h1 k
      rw [← hk]
      exact this
    · obtain ⟨k, hk⟩ := List.mem_iff_get.mp (List.mem_filter.mpr ⟨List.mem_finRange r, hr⟩)
      have := h2 k
      rw [← hk]
      exact this
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => ?_, fun k => ?_⟩
    · exact h1 _ (List.mem_filter.mp (List.get_mem _ _)).2
    · exact h2 _ (List.mem_filter.mp (List.get_mem _ _)).2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
