import CORALean.ContSet.VPolytope.Real.Operations.Interval

/-!
# `VPolytope.interval` contains the polytope

Coordinatewise, and the same argument at both ends: a convex combination of
values each below the supremum is below it too, the weights summing to one.

Nothing here needs the vertex set to be nonempty — at no vertices the weights
cannot sum to one, so there is nothing to bound.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

theorem VPolytope.interval_outer (P : VPolytope (Vec ℝ n)) :
    P.construct ⊆ P.interval.construct := by
  rintro _ ⟨β, hβ, hsum, rfl⟩ i
  have hbddA : BddAbove (Set.range fun l => P.V l i) := (Set.finite_range _).bddAbove
  have hbddB : BddBelow (Set.range fun l => P.V l i) := (Set.finite_range _).bddBelow
  have hx : (∑ l, β l • P.V l) i = ∑ l, β l * P.V l i := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · show (⨅ l, P.V l i) ≤ (∑ l, β l • P.V l) i
    rw [hx]
    calc (⨅ l, P.V l i) = (∑ l, β l) * ⨅ l, P.V l i := by rw [hsum, one_mul]
      _ = ∑ l, β l * ⨅ l', P.V l' i := by rw [Finset.sum_mul]
      _ ≤ ∑ l, β l * P.V l i := Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_left (ciInf_le hbddB l) (hβ l)
  · show (∑ l, β l • P.V l) i ≤ ⨆ l, P.V l i
    rw [hx]
    calc ∑ l, β l * P.V l i ≤ ∑ l, β l * ⨆ l', P.V l' i := Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_left (le_ciSup hbddA l) (hβ l)
      _ = (∑ l, β l) * ⨆ l, P.V l i := by rw [Finset.sum_mul]
      _ = ⨆ l, P.V l i := by rw [hsum, one_mul]

end CORALean.Real
