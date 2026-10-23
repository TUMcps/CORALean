module

public import CORALean.ContSet.HPolytope.Real.Operations.CompactZeros
public import CORALean.ContSet.HPolytope.Real.Theorems.ConstructEmptySet
public import CORALean.ContSet.HPolytope.Real.Theorems.NormalizeRowsExact
public import CORALean.ContSet.HPolytope.Real.Theorems.RestrictConstruct

@[expose] public section

/-!
# `compactZeros` denotes the same set, exactly

A zero row `0 ≤ b` with `b ≥ 0` or `0 = 0` holds at every point, so deleting it changes nothing;
an infeasible one empties the set, and the empty set is what is returned.

## Inputs
* `P` – H-polytope

## Hypotheses
* none

## Conclusion
* `compactZeros` denotes the same set, exactly
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.compactZeros_exact (P : HPolytope (Vec ℝ n)) : -- --- CONCL ---
    P.compactZeros.construct = P.construct := by -- --- PROOF ---
  rw [← P.normalizeRows_exact]
  unfold HPolytope.compactZeros
  generalize P.normalizeRows = Q
  simp only []
  split_ifs with h
  · -- infeasible zero row: both sets are empty
    have hQ : Q.construct = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x hx => ?_
      rcases h with ⟨i, hA, hb⟩ | ⟨r, hA, hb⟩
      · have := hx.1 i
        rw [hA] at this
        simp at this
        linarith
      · have := hx.2 r
        rw [hA] at this
        simp at this
        exact hb this.symm
    -- and so is the empty set
    rw [hQ]
    exact HPolytope.construct_emptySet
  · -- no infeasible row: the zero rows hold everywhere
    push Not at h
    rw [HPolytope.restrict_construct]
    ext x
    simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and, HPolytope.construct]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun r => ?_⟩
      · by_cases hz : Q.A i = 0
        · rw [hz]; simpa using h.1 i hz
        · exact h1 i hz
      · by_cases hz : Q.Ae r = 0
        · rw [hz]; simpa using (h.2 r hz).symm
        · exact h2 r hz
    · rintro ⟨h1, h2⟩
      exact ⟨fun i _ => h1 i, fun r _ => h2 r⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
