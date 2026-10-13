import CORALean.ContSet.PolyZonotope.Real.Operations.OfPoint
import CORALean.ContSet.ConPolyZono.Real.Operations.NoZeroCol
import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialEqZeroOfNoZeroCol

/-!
# A polynomial zonotope with no zero exponent column contains its centre

CORA's `center` returns the field `c` with no guarantee. The guarantee is `NoZeroCol`: every
monomial then vanishes at the factor vector `0`, so `c` is the point of the zero factors and
zero independent coefficients. Without it a column `0` is a constant monomial `1`, and `c`
need not lie in the set (one generator `1` with exponent column `0` denotes `{c + 1}`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.centre_mem_construct (pZ : PolyZonotope α)
    (hE : ConPolyZono.NoZeroCol pZ.E) : pZ.c ∈ pZ.construct := by
  refine ⟨fun _ => 0, fun _ => 0, fun k => by simp, fun j => by simp, ?_⟩
  simp [ConPolyZono.monomial_eq_zero_of_noZeroCol hE (fun _ => rfl)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
