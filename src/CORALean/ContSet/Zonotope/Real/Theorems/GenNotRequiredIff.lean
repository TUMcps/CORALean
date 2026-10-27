module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Zonotope.Real.Theorems.GenRemovableIff

@[expose] public section

/-!
# [1, Prop. 2]: when a generator is no longer required

The printed biconditional, over `gen_removable_iff`'s counting half. "No longer required" is read
as [1]'s own proof reads it: the difference is still cut out by the rows of `C` that `g⁽ᵐ'ⁱ⁾`
does not span. `hrows` is [1, Thm. 3] at the rows `C`/`d`, kept as a hypothesis so that `C` and
`d` stay free; at `minkDiffRowNormal`/`minkDiffRowOffset` it is `minkowskiDiff_rows_eq`, and
`gen_not_required_iff_of_span` is this with it discharged. `hmin` and `hirr` are the *minimum*
H-representation: dropping every row of `Red` still describes the difference, and no row outside
`Red` is redundant. `hmin` carries the step [1] makes in one sentence: jointly redundant is not
individually redundant; the fact that rules that out is `rows_eq_drop_redundant`.

## Inputs
* `n` – dimension minus two
* `Zm` – minuend
* `Zs` – subtrahend
* `C` – row normals
* `d` – row offsets
* `Red` – redundant rows
* `i` – generator index

## Hypotheses
* `hRed` – redundant rows have `n + 1` generators
* `hrows` – rows describe the Minkowski difference
* `hmin` – non-redundant rows suffice
* `hirr` – non-redundant rows irredundant

## Conclusion
* the count is reached iff the rows without generator `i` suffice

## References

* [1] [M. Althoff. "On Computing the Minkowski Difference of Zonotopes". arXiv preprint
      arXiv:1512.02794,
      2015.](../../../../../../references/2015/althoff-arxiv-minkowski-difference.md)
-/

-- Authors:       Claude Opus 5
-- Written:       21-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2]: the printed count is reached exactly when the rows the `i`-th
generator does not span already describe the Minkowski difference. -/
theorem Zonotope.gen_not_required_iff {n : ℕ} (Zm Zs : Zonotope (Vec ℝ (n + 2)))
    (C : Bool × Finset (Fin Zm.h) → (Vec ℝ (n + 2) →ₗ[ℝ] ℝ))
    (d : Bool × Finset (Fin Zm.h) → ℝ) (Red : Finset (Bool × Finset (Fin Zm.h)))
    (hRed : ∀ j ∈ Red, j.2.card = n + 1)
    (hrows : minkowskiDiff Zm.construct Zs.construct
      = {x | ∀ j, j.2.card = n + 1 → C j x ≤ d j})
    (hmin : minkowskiDiff Zm.construct Zs.construct
      = {x | ∀ j, j.2.card = n + 1 → j ∉ Red → C j x ≤ d j})
    (hirr : ∀ j, j.2.card = n + 1 → j ∉ Red →
      ¬{x | ∀ k, k.2.card = n + 1 → k ≠ j → C k x ≤ d k} ⊆ {x | C j x ≤ d j})
    (i : Fin Zm.h) : -- --- CONCL ---
    ∑ j ∈ Red, (if i ∈ j.2 then 1 else 0) = 2 * (Zm.h - 1).choose n
      ↔ minkowskiDiff Zm.construct Zs.construct
          = {x | ∀ j, j.2.card = n + 1 → i ∉ j.2 → C j x ≤ d j} := by -- --- PROOF ---
  classical
  constructor
  · -- every row `i` spans is redundant, so what is left of `Red` spans none of them
    intro hsum
    have hin := (Zm.gen_removable_iff Red hRed i).mp hsum
    refine Set.eq_of_subset_of_subset (fun x hx => ?_) (fun x hx => ?_)
    · rw [hrows] at hx
      exact fun j hj _ => hx j hj
    · rw [hmin]
      intro j hj hjRed
      refine hx j hj fun hij => hjRed ?_
      simpa using hin j.1 j.2 hj hij
  · -- conversely, a row `i` spans that survived would be irredundant, and none is
    intro hdrop
    refine (Zm.gen_removable_iff Red hRed i).mpr fun b S hS hiS => ?_
    by_contra hnot
    refine hirr (b, S) hS hnot fun x hx => ?_
    have hxP : x ∈ minkowskiDiff Zm.construct Zs.construct := by
      rw [hdrop]
      exact fun j hj hij => hx j hj (by rintro rfl; exact hij hiS)
    rw [hrows] at hxP
    exact hxP (b, S) hS

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
