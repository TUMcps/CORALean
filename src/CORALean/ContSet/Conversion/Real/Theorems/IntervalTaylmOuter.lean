module

public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.MonomialSingle
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Conversion.Real.Operations.Basic

@[expose] public section

/-!
# A box as an array of Taylor models

`Interval.taylm_outer`: its `taylm` encloses it.

## Inputs
* `I` – interval
* `N` – Taylor order
* `i` – coordinate

## Hypotheses
* none

## Conclusion
* Taylor model encloses the midpoint-radius parametrisation
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.taylm_outer (I : Interval (Vec ℝ n)) (N : ℕ) (i : Fin n) :
    (I.taylm N i).Encloses fun t =>
      (I.inf i + I.sup i) / 2 + (I.sup i - I.inf i) / 2 * t i := by
  intro t _
  simp [Interval.taylm, Taylm.poly, Taylm.monomial_zero, Taylm.monomial_single]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
