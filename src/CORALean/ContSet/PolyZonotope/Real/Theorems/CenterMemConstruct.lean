module

public import CORALean.ContSet.PolyZonotope.Real.Operations.OfPoint
public import CORALean.ContSet.ConPolyZono.Real.Operations.NoZeroCol
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialEqZeroOfNoZeroCol

@[expose] public section

/-!
# A polynomial zonotope with no zero exponent column contains its center

CORA's `center` returns the field `c` with no guarantee. The guarantee is `NoZeroCol`: every
monomial then vanishes at the factor vector `0`, so `c` is the point of the zero factors and
zero independent coefficients. Without it a column `0` is a constant monomial `1`, and `c`
need not lie in the set (one generator `1` with exponent column `0` denotes `{c + 1}`).

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* `hE` – no exponent column is zero

## Conclusion
* the center lies in the set
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.center_mem_construct (pZ : PolyZonotope α)
    (hE : ConPolyZono.NoZeroCol pZ.E) : pZ.c ∈ pZ.construct := by
  refine ⟨fun _ => 0, fun _ => 0, fun k => by simp, fun j => by simp, ?_⟩
  simp [ConPolyZono.monomial_eq_zero_of_noZeroCol hE (fun _ => rfl)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
