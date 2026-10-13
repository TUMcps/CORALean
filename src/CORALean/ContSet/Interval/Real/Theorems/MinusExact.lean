import CORALean.ContSet.Interval.Real.Theorems.MinusOuter
import CORALean.ContSet.Interval.Real.Theorems.PlusExact

/-!
# `Interval.minus` is exactly the pointwise difference of the sets

Both boxes `IsNonempty`, as `plus_exact` needs: `[1, 0] - [0, 10]` is `∅` as a set but `[-9, 0]` by
the definition. `minus_outer` is the half that needs no such hypothesis.

[1, Eq. 2]: `[x] - [y] = [x̲ - y̅, x̅ - y̲]`.

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.minus_exact (I₁ I₂ : Interval α) (h₁ : I₁.IsNonempty) (h₂ : I₂.IsNonempty) :
    I₁.construct - I₂.construct = (I₁.minus I₂).construct := by -- --- PROOF ---
  refine Set.eq_of_subset_of_subset (Interval.minus_outer I₁ I₂) fun x hx => ?_
  -- the negated box is nonempty, so the sum is exact
  have h₂' : I₂.uminus.IsNonempty := fun i => by
    show entry (-I₂.sup) i ≤ entry (-I₂.inf) i
    rw [Entrywise.entry_neg, Entrywise.entry_neg]
    linarith [h₂ i]
  rw [Interval.minus_eq_plus_uminus, ← Interval.plus_exact I₁ I₂.uminus h₁ h₂'] at hx
  obtain ⟨a, ha, c, hc, rfl⟩ := hx
  rw [← Interval.uminus_exact] at hc
  exact ⟨a, ha, -c, Set.mem_neg.1 hc, sub_neg_eq_add a c⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
