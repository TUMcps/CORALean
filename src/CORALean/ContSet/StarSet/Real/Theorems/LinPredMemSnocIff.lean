module

public import CORALean.ContSet.StarSet.Real.Operations.Basic
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# What `StarSet.LinPred.snoc` admits

The old factors with one more appended meet the extended predicate exactly when the old ones meet
the old predicate and the new one lies in its range: every old row reads the new factor through its
padded zero as nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The new factor in its range, the old ones meeting the old predicate, which reads no new one. -/
theorem StarSet.LinPred.mem_snoc_iff {m : ℕ} {p : StarSet.LinPred m} {lo hi t : ℝ} {α : Vec ℝ m} :
    (Fin.snoc (α := fun _ => ℝ) α t : Vec ℝ (m + 1)) ∈ ContSet.construct (p.snoc lo hi)
      ↔ α ∈ ContSet.construct p ∧ lo ≤ t ∧ t ≤ hi := by -- --- PROOF ---
  simp only [ContSet.construct, StarSet.LinPred.construct, StarSet.LinPred.snoc,
    Set.mem_setOf_eq, List.mem_map, Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last,
    Fin.sum_univ_castSucc]
  constructor
  · rintro ⟨⟨hb, ht⟩, h⟩
    exact ⟨⟨hb, fun r hr => by simpa using h _ ⟨r, hr, rfl⟩⟩, ht⟩
  · rintro ⟨⟨hb, h⟩, ht⟩
    refine ⟨⟨hb, ht⟩, fun _ ⟨r, hr, e⟩ => ?_⟩
    subst e
    simpa using h r hr

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
