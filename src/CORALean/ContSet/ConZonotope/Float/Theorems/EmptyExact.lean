module

public import CORALean.ContSet.ConZonotope.Float.Operations.Empty
public import CORALean.ContSet.HPolytope.Float.Theorems.ConstructEmptySet

@[expose] public section

/-!
# `ConZonotope.empty` denotes the empty set

The constraint `HPolytope.emptySet` admits no coefficient family, so the nominal part
is `∅`, and so is its sum with the error box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.empty_exact (n : ℕ) :
    (ConZonotope.empty n : ConZonotope 𝕋 (Vec 𝕋 n)).construct = ∅ := by -- --- PROOF ---
  have hN : InflatedContSet.nominalSet (ConZonotope.empty n : ConZonotope 𝕋 (Vec 𝕋 n)) = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨β, -, hβ, -⟩
    have h : β ∈ (HPolytope.emptySet 𝕋 0).construct := (HPolytope.mem_nominal_of_origin rfl).mpr hβ
    rw [HPolytope.construct_emptySet] at h
    exact h
  show InflatedContSet.nominalSet (ConZonotope.empty n : ConZonotope 𝕋 (Vec 𝕋 n))
      + (ConZonotope.empty n : ConZonotope 𝕋 (Vec 𝕋 n)).I_error.construct = _
  rw [hN, Set.empty_add]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
