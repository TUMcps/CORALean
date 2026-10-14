module

public import CORALean.Global.Float.Instances.Dyadic.Operations.Basic
public import CORALean.Global.Float.Instances.Dyadic.Theorems.TwoZpowCoarsen
public import Mathlib.Analysis.Normed.Ring.Lemmas

@[expose] public section

/-!
# Coarsening down never overshoots

`Int.ediv_mul_le` on the mantissa, read at the shift `(e - exponent).toNat` that
`two_zpow_coarsen` aligns.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem coarsenDown_le (e : ℤ) (d : Dyadic p) :
    toReal (coarsenDown e d) ≤ toReal d := by -- --- PROOF ---
  have h : d.mantissa / 2 ^ (e - d.exponent).toNat * 2 ^ (e - d.exponent).toNat ≤ d.mantissa :=
    Int.ediv_mul_le _ (pow_ne_zero _ two_ne_zero)
  rw [coarsenDown, toReal_def, toReal_def, Int.shiftRight_eq_div_pow, ← two_zpow_coarsen d e,
    ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (zpow_pos two_pos _))
  exact_mod_cast h

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
