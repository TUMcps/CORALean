import CORALean.ContSet.ConPolyZono.Real.Operations.ConsCol

/-!
# A constraint matrix applied to a factor vector is a sum of columns

`A μ(α)` read as a generator sum over the constraint columns, at the monomials
`EC` names — the form `sum_monomial_merge` merges.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- `A μ(α)` read as a generator sum over the constraint columns, at the
monomials `EC` names — the form `sum_monomial_merge` merges. -/
theorem ConPolyZono.mulVec_eq_sum {m s : ℕ} (A : Mat ℝ m s) (v : Vec ℝ s) :
    A *ᵥ v = ∑ l, v l • ConPolyZono.consCol A l := by
  funext i
  show (∑ l, A i l * v l) = (∑ l, v l • ConPolyZono.consCol A l) i
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
