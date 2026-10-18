module

public import CORALean.ContSet.Zonotope.Real.Theorems.GenNotRequiredIffOfSpan
public import CORALean.ContSet.Zonotope.Real.Theorems.RowsEqDropRedundant

@[expose] public section

/-!
# [1, Prop. 2] with the redundant rows computed, not assumed

`Zonotope.gen_not_required_iff_of_span` with `Red` the set of redundant rows of [1, Thm. 3] and
its two hypotheses `hmin` and `hirr` discharged. `hirr` is what `Red` being exactly the redundant
rows says. `hmin`, that the remaining rows still describe `Z_m ⊖ Z_s`, is
`rows_eq_drop_redundant`, which needs two things [1] does not print: the difference has nonempty
interior, and no two rows cut the same proper halfspace (for [1, Thm. 2]'s rows, the minuend's
generators in general position). Without the second, one halfspace cut twice is two redundant
rows that cannot both go, and the printed count would call a generator droppable that is not.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

open Classical in
/-- [1, Prop. 2] for a full-dimensional difference whose rows cut distinct proper halfspaces, `Red`
the rows the others imply. -/
theorem Zonotope.gen_not_required_iff_of_fullDim {n : ℕ} (Zm Zs : Zonotope (Vec ℝ (n + 2)))
    (hspan : Submodule.span ℝ (Set.range Zm.G) = ⊤)
    (hint : (interior (minkowskiDiff Zm.construct Zs.construct)).Nonempty)
    (hdist : ∀ j k : Bool × Finset (Fin Zm.h), j.2.card = n + 1 → k.2.card = n + 1 → j ≠ k →
      {x | dotProductEquiv ℝ _ (Zm.minkDiffRowNormal j) x ≤ Zm.minkDiffRowOffset Zs j}
        = {x | dotProductEquiv ℝ _ (Zm.minkDiffRowNormal k) x ≤ Zm.minkDiffRowOffset Zs k} →
      {x | dotProductEquiv ℝ _ (Zm.minkDiffRowNormal j) x ≤ Zm.minkDiffRowOffset Zs j}
        = Set.univ)
    (i : Fin Zm.h) : -- --- STMT ---
    ∑ j ∈ Finset.univ.filter (fun j : Bool × Finset (Fin Zm.h) => j.2.card = n + 1 ∧
        {x | ∀ k : Bool × Finset (Fin Zm.h), k.2.card = n + 1 → k ≠ j →
            dotProductEquiv ℝ _ (Zm.minkDiffRowNormal k) x ≤ Zm.minkDiffRowOffset Zs k}
          ⊆ {x | dotProductEquiv ℝ _ (Zm.minkDiffRowNormal j) x ≤ Zm.minkDiffRowOffset Zs j}),
        (if i ∈ j.2 then 1 else 0) = 2 * (Zm.h - 1).choose n
      ↔ minkowskiDiff Zm.construct Zs.construct
          = {x | ∀ j, j.2.card = n + 1 → i ∉ j.2 →
              dotProductEquiv ℝ _ (Zm.minkDiffRowNormal j) x ≤
                Zm.minkDiffRowOffset Zs j} := by -- --- PROOF ---
  have hrows := Zm.minkowskiDiff_rows_eq Zs hspan
  refine Zm.gen_not_required_iff_of_span Zs hspan _ (fun j hj => (Finset.mem_filter.mp hj).2.1)
    ?_ ?_ i
  · -- `hmin`: every redundant row dropped at once
    rw [hrows]
    exact Zonotope.rows_eq_drop_redundant _ _ _ _ (hrows ▸ hint) hdist
      fun j hj _ => (Finset.mem_filter.mp hj).2.2
  · -- `hirr`: a row outside the filter is not redundant
    intro j hj hjR hsub
    exact hjR (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hsub⟩)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
