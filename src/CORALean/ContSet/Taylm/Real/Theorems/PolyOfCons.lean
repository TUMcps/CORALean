module

public import CORALean.ContSet.Taylm.Real.Taylm

@[expose] public section

/-!
# `Taylm.polyOf_cons`

The polynomial of a term list unfolds one term at a time.

## Inputs
* `a` – first term
* `L` – remaining terms
* `t` – point

## Hypotheses
* none

## Conclusion
* the polynomial of a prepended term adds that term's value
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

@[simp] theorem Taylm.polyOf_cons (a : ℝ × (Fin n → ℕ)) (L : List (ℝ × (Fin n → ℕ)))
    (t : Vec ℝ n) :
    Taylm.polyOf (a :: L) t = a.1 * Taylm.monomial a.2 t + Taylm.polyOf L t := by
  simp [Taylm.polyOf]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
