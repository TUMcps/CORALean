import CORALean.ContSet.LevelSet.Real.Operations.SplitEquality
import CORALean.ContSet.LevelSet.Real.Theorems.RestrictConstruct

/-!
# Splitting a level set is exact

The level set is the intersection of the equality part and the rest, an equality of sets.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Exact: `L` is the equality part intersected with the rest. -/
theorem LevelSet.splitEquality_exact {n : ℕ} (L : LevelSet n) :
    L.construct = L.splitEquality.1.construct ∩ L.splitEquality.2.construct := by -- --- PROOF ---
  ext x
  show x ∈ L.construct ↔ x ∈ (L.restrict _).construct ∩ (L.restrict _).construct
  rw [Set.mem_inter_iff, LevelSet.restrict_construct, LevelSet.restrict_construct]
  simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  change (∀ i, _) ↔ _
  constructor
  · intro h
    exact ⟨fun i _ => h i, fun i _ => h i⟩
  · rintro ⟨h1, h2⟩ i
    by_cases hi : L.op i = .eq
    · exact h1 i hi
    · exact h2 i hi

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
