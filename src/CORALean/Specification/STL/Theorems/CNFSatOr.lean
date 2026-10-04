import CORALean.Specification.STL.Operations.CNFOr
import CORALean.Specification.STL.Theorems.CNFSatToFormula
import CORALean.Specification.STL.Theorems.ClauseHoldsMerge

/-!
# The disjunction of normal forms holds iff one does

`ξ ⊨ₜ a ∨ b ⇔ ξ ⊨ₜ a ∨ ξ ⊨ₜ b` for `a.or b`: the distribution of [1, Sec. 4.1], a clause of the
result being the merge of a clause of each.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.CNF.sat_or (c : ℝ≥0) (a b : STL.CNF X) (ξ : ℝ≥0 → X) :
    ((a.or b).toFormula c).Sat ξ ↔
      (a.toFormula c).Sat ξ ∨ (b.toFormula c).Sat ξ := by -- --- PROOF ---
  rw [STL.CNF.sat_toFormula, STL.CNF.sat_toFormula, STL.CNF.sat_toFormula]
  simp only [STL.CNF.or, List.mem_flatMap, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    obtain ⟨⟨x, hx, hPx⟩, ⟨y, hy, hQy⟩⟩ := hn
    -- the merge of the two refuting clauses is refuted by neither
    rcases (STL.Clause.holds_merge c x y ξ).1 (h _ x hx y hy rfl) with ⟨z, hz, hh⟩ | ⟨z, hz, hh⟩
    · exact hPx z hz hh
    · exact hQy z hz hh
  · rintro (h | h) clause x hx y hy rfl
    · obtain ⟨z, hz, hh⟩ := h x hx
      exact (STL.Clause.holds_merge c x y ξ).2 (Or.inl ⟨z, hz, hh⟩)
    · obtain ⟨z, hz, hh⟩ := h y hy
      exact (STL.Clause.holds_merge c x y ξ).2 (Or.inr ⟨z, hz, hh⟩)


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
