import CORALean.ContSet.Zonotope.Real.Theorems.GenNotRequiredIff
import CORALean.ContSet.Zonotope.Real.Theorems.MinkowskiDiffRowsEq

/-!
# [1, Prop. 2]: when a generator is no longer required, without the `Thm. 3` hypothesis

`Zonotope.gen_not_required_iff` at the rows of [1, Thm. 3] themselves, `Zonotope.minkDiffRowNormal`
and `Zonotope.minkDiffRowOffset`, where `hrows` is the theorem `Zonotope.minkowskiDiff_rows_eq`,
at [1, Thm. 2]'s own hypothesis that the minuend's generators span. The minimum H-representation
`hmin`/`hirr` stays a hypothesis here; `gen_not_required_iff_of_fullDim` discharges it.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2] at [1, Thm. 3]'s own rows: the printed count is reached exactly when the rows the
`i`-th generator does not span already describe the Minkowski difference. -/
theorem Zonotope.gen_not_required_iff_of_span {n : ℕ} (Zm Zs : Zonotope (Vec ℝ (n + 2)))
    (hspan : Submodule.span ℝ (Set.range Zm.G) = ⊤)
    (Red : Finset (Bool × Finset (Fin Zm.h))) (hRed : ∀ j ∈ Red, j.2.card = n + 1)
    (hmin : minkowskiDiff Zm.construct Zs.construct
      = {x | ∀ j, j.2.card = n + 1 → j ∉ Red →
          dotProductEquiv ℝ _ (Zm.minkDiffRowNormal j) x ≤ Zm.minkDiffRowOffset Zs j})
    (hirr : ∀ j, j.2.card = n + 1 → j ∉ Red →
      ¬{x | ∀ k, k.2.card = n + 1 → k ≠ j →
          dotProductEquiv ℝ _ (Zm.minkDiffRowNormal k) x ≤ Zm.minkDiffRowOffset Zs k}
        ⊆ {x | dotProductEquiv ℝ _ (Zm.minkDiffRowNormal j) x ≤ Zm.minkDiffRowOffset Zs j})
    (i : Fin Zm.h) :
    ∑ j ∈ Red, (if i ∈ j.2 then 1 else 0) = 2 * (Zm.h - 1).choose n
      ↔ minkowskiDiff Zm.construct Zs.construct
          = {x | ∀ j, j.2.card = n + 1 → i ∉ j.2 →
              dotProductEquiv ℝ _ (Zm.minkDiffRowNormal j) x ≤ Zm.minkDiffRowOffset Zs j} :=
  Zm.gen_not_required_iff Zs (fun j => dotProductEquiv ℝ _ (Zm.minkDiffRowNormal j))
    (Zm.minkDiffRowOffset Zs) Red hRed (Zm.minkowskiDiff_rows_eq Zs hspan) hmin hirr i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
