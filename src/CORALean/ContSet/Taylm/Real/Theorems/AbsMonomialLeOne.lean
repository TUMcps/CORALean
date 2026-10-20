module

public import CORALean.ContSet.Taylm.Real.Taylm

@[expose] public section

/-!
# `Taylm.abs_monomial_le_one`

## Inputs
* `t` – point
* `e` – exponents

## Hypotheses
* `ht` – point lies in the unit box

## Conclusion
* the monomial has magnitude at most one
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- On the box every monomial is in `[-1, 1]`, which is what a rounded coefficient pays. -/
theorem Taylm.abs_monomial_le_one {t : Vec ℝ n} (ht : t ∈ Taylm.box n) (e : Fin n → ℕ) :
    |Taylm.monomial e t| ≤ 1 := by
  rw [Taylm.monomial, Finset.abs_prod]
  exact Finset.prod_le_one (fun k _ => abs_nonneg _) fun k _ => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (ht k)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
