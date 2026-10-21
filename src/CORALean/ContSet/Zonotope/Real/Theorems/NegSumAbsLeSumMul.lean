module

public import CORALean.Global.Tensor
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A combination with factors in the unit box is at least minus the absolute sum

`-Σ_{j ∈ s} |a(j)| ≤ Σ_{j ∈ s} β(j) a(j)` for `|β(j)| ≤ 1`: the lower end of the support of a
zonotope along a functional whose values on the generators are `a`, over any part `s` of them.

## Inputs
* `q` – number of generators
* `s` – generator indices
* `β` – factors
* `a` – values on the generators

## Hypotheses
* `hβ` – the factors lie in the unit box

## Conclusion
* the factor-weighted sum is at least `-Σ |a|`
-/

-- Authors:       Claude Opus 5.5
-- Written:       21-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `-Σ |a(j)| ≤ Σ β(j) a(j)` for factors in the unit box. -/
theorem Zonotope.neg_sum_abs_le_sum_mul {q : ℕ} (s : Finset (Fin q)) (β a : Fin q → ℝ)
    (hβ : ∀ j, |β j| ≤ 1) : -- --- CONCL ---
    -∑ j ∈ s, |a j| ≤ ∑ j ∈ s, β j * a j := by -- --- PROOF ---
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : |β j * a j| ≤ |a j| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hβ j)
  linarith [neg_abs_le (β j * a j)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
