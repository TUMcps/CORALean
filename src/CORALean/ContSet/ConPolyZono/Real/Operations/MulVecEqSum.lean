module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic

@[expose] public section

/-!
# A constraint matrix applied to a factor vector is a sum of columns

`A μ(α)` read as a generator sum over the constraint columns, at the monomials
`R` names — the form `sum_monomial_merge` merges.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- `A μ(α)` read as a generator sum over the constraint columns, at the
monomials `R` names — the form `sum_monomial_merge` merges. -/
theorem ConPolyZono.mulVec_eq_sum {m q : ℕ} (A : Mat ℝ m q) (v : Vec ℝ q) :
    A *ᵥ v = ∑ l, v l • ConPolyZono.consCol A l := by
  funext i
  show (∑ l, A i l * v l) = (∑ l, v l • ConPolyZono.consCol A l) i
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
