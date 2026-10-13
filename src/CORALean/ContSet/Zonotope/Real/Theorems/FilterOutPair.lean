import CORALean.ContSet.Zonotope.Real.Operations.FilterOut

/-!
# `filterOut` deletes both of two equal cells

Two equal cells each have the other as the cover that empties their remainder, so neither
survives, and the kept list is empty although each cell is a nonempty set. The union of the kept
cells is not the union of all of them, which is what "deletes parallelotopes that are covered by
other parallelotopes" is used for. The statement is for CORA's intended criterion
(`Zonotope.filterOut`); CORA's code does not run (FINDINGS.md).

Source: [1].

## References

* [1] `contSet/@zonotope/filterOut.m`, CORA (Sep. 2025).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.filterOut_pair (Z : Zonotope (Vec ℝ n)) :
    Zonotope.filterOut ![Z, Z] = ∅ := by -- --- PROOF ---
  ext i
  have hdiff : Z.construct \ ⋃ j, ⋃ (_ : j ≠ i), (![Z, Z] j).construct = ∅ := by
    refine Set.sdiff_eq_empty.mpr fun x hx => ?_
    simp only [Set.mem_iUnion, exists_prop]
    fin_cases i
    · exact ⟨1, by decide, by simpa using hx⟩
    · exact ⟨0, by decide, by simpa using hx⟩
  simp only [Zonotope.filterOut, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rw [show (![Z, Z] i) = Z by fin_cases i <;> rfl, hdiff, interior_empty]
  exact Set.not_nonempty_empty

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
