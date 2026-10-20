module

public import CORALean.Global.Float.Instances.Dyadic.Operations.CoarsenUp
public import CORALean.Global.Float.Instances.Dyadic.Theorems.TwoZpowAlign

@[expose] public section

/-!
# The alignment of a coarsening

`two_zpow_align` at the shift `(e - exponent).toNat` and the exponent `max exponent e` that
`coarsenUp` and `coarsenDown` use.

## Inputs
* `d` – dyadic
* `e` – target exponent

## Hypotheses
* none

## Conclusion
* the alignment power times the dyadic's own power is the power at the larger exponent
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem two_zpow_coarsen (d : Dyadic p) (e : ℤ) :
    (2 : ℝ) ^ (e - d.exponent).toNat * 2 ^ d.exponent = 2 ^ max d.exponent e := by
  have h : d.exponent ≤ max d.exponent e := le_max_left _ _
  have hk : (e - d.exponent).toNat = (max d.exponent e - d.exponent).toNat := by omega
  rw [hk]
  exact two_zpow_align h

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
