module

public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil

@[expose] public section

/-!
# `Taylm.polyOf_append`

The polynomial of an appended term list is the sum of the polynomials.

## Inputs
* `L₁` – first terms
* `L₂` – second terms
* `t` – point

## Hypotheses
* none

## Conclusion
* the polynomial of joined term lists is the sum of the two values
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.polyOf_append (L₁ L₂ : List (ℝ × (Fin n → ℕ))) (t : Vec ℝ n) :
    Taylm.polyOf (L₁ ++ L₂) t = Taylm.polyOf L₁ t + Taylm.polyOf L₂ t := by
  simp [Taylm.polyOf]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
