import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Zonotope.Real.Theorems.GenRemovableIff

/-!
# [1, Prop. 2]: when a generator is no longer required

The printed biconditional, over `gen_removable_iff`'s counting half. "The `i`-th generator is no
longer required for the difference" is read as [1]'s own proof reads it: the difference is still cut
out by the rows of `C` that `g⁽ᵐ'ⁱ⁾` does not span.

`hrows` is [1, Thm. 3] at the rows `C`/`d`, kept as a hypothesis here so that `C` and `d` stay
free. At `Zonotope.minkDiffRowNormal`/`Zonotope.minkDiffRowOffset` it is the theorem
`Zonotope.minkowskiDiff_rows_eq`, and `Zonotope.gen_not_required_iff_of_span` is this statement with
it discharged. `hmin` and `hirr` are the *minimum* H-representation: dropping every row
of `Red` still describes the difference, and no row outside `Red` is redundant, so `Red` is exactly
the redundant set. The paper obtains it by linear programming; nothing here computes it, and nothing
here proves one exists.

`hmin` is what carries the step [1] makes in one sentence. Each row of `Red` being redundant on its
own would not give it — two rows cutting the same halfspace are each redundant and jointly are not —
and the classical fact that rules that out for a full-dimensional polytope, that its irredundant
halfspaces already describe it, is polytope theory Mathlib has not got.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Tobias Ladner
-- Written:       21-September-2026
-- Last update:   ---
-- Last revision: ---


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
    (i : Fin Zm.h) :
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
