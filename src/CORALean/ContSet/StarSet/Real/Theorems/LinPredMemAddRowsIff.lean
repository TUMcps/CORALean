module

public import CORALean.ContSet.StarSet.Real.Operations.Basic
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# What `StarSet.LinPred.addRows` admits

The coefficients meet the extended predicate exactly when they meet the old one and every added
row.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The added rows are met besides the predicate's own. -/
theorem StarSet.LinPred.mem_addRows_iff {m : ℕ} {p : StarSet.LinPred m}
    {rs : List ((Fin m → ℝ) × ℝ)} {α : Vec ℝ m} :
    α ∈ ContSet.construct (p.addRows rs)
      ↔ α ∈ ContSet.construct p ∧ ∀ r ∈ rs, ∑ k, r.1 k * α k ≤ r.2 := by
  simp only [ContSet.construct, StarSet.LinPred.construct, StarSet.LinPred.addRows,
    Set.mem_setOf_eq, List.mem_append]
  exact ⟨fun ⟨hb, h⟩ => ⟨⟨hb, fun r hr => h r (Or.inl hr)⟩, fun r hr => h r (Or.inr hr)⟩,
    fun ⟨⟨hb, h⟩, h'⟩ => ⟨hb, fun r hr => hr.elim (h r) (h' r)⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
