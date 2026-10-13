import CORALean.ContSet.PolyZonotope.Real.Operations.Compact

/-!
# How large `compact`'s result is

Bounds and not counts, and the only file here that is neither: how many columns
survive a merge depends on how many of them were equal, which nothing in the
operand's *sizes* fixes. What does hold at every operand is that compaction
never grows anything — it keeps a sub-`Finset` of the columns and a sub-`Finset`
of the factors, and leaves the independent block alone.

That is what `Complexity/Time/Reduce.lean` needs: it prices the ranking at the operand's
own counts, which is an upper bound exactly because compaction cannot have made
them larger.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The kept columns are a sub-`Finset` of all of them, so there are no more. -/
theorem PolyZonotope.compact_h_le (pZ : PolyZonotope α) : pZ.compact.h ≤ pZ.h := by
  have h := Finset.card_le_univ (PolyZonotope.compactKeep pZ.E pZ.G)
  rw [Fintype.card_fin] at h
  exact h

/-- The kept factors likewise, over the columns the merge left. -/
theorem PolyZonotope.compact_p_le (pZ : PolyZonotope α) : pZ.compact.p ≤ pZ.p := by
  have h := Finset.card_le_univ (PolyZonotope.usedFactors pZ.compactGens.E)
  rw [Fintype.card_fin] at h
  exact h

/-- The independent block is untouched by either half of the compaction. -/
theorem PolyZonotope.compact_q (pZ : PolyZonotope α) : pZ.compact.q = pZ.q := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
