module

public import CORALean.ContSet.Taylm.Real.Taylm

@[expose] public section

/-!
# `Taylm.monomial_single`

The monomial of the exponent vector with a single `1` at `j` is the variable `t j`.

## Inputs
* `j` – coordinate
* `t` – point

## Hypotheses
* none

## Conclusion
* the monomial of a unit exponent is that coordinate
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.monomial_single (j : Fin n) (t : Vec ℝ n) :
    Taylm.monomial (Pi.single j 1) t = t j := by
  rw [Taylm.monomial, Finset.prod_eq_single j]
  · simp
  · intro k _ hk; simp [hk]
  · intro h; exact absurd (Finset.mem_univ j) h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
