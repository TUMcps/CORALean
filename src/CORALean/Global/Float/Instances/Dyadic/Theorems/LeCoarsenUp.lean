import CORALean.Global.Float.Instances.Dyadic.Operations.CoarsenUp
import CORALean.Global.Float.Instances.Dyadic.Theorems.TwoZpowCoarsen
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Coarsening up never undershoots

The same floor-division fact as for `roundUp`, `Int.ediv_mul_le` on the negated mantissa,
read at the shift `(e - exponent).toNat` that `two_zpow_coarsen` aligns.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_coarsenUp (e : ℤ) (d : Dyadic p) :
    toReal d ≤ toReal (coarsenUp e d) := by -- --- PROOF ---
  have h : d.mantissa ≤
      -((-d.mantissa) / 2 ^ (e - d.exponent).toNat) * 2 ^ (e - d.exponent).toNat := by
    rw [neg_mul, le_neg]
    exact Int.ediv_mul_le _ (pow_ne_zero _ two_ne_zero)
  rw [coarsenUp, toReal_def, toReal_def, Int.shiftRight_eq_div_pow, ← two_zpow_coarsen d e,
    ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (zpow_pos two_pos _))
  exact_mod_cast h

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
