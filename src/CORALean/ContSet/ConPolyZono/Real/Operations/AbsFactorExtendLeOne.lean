module

public import CORALean.ContSet.ConPolyZono.Real.Operations.FactorExtend
public import CORALean.ContSet.PolyZonotope.Real.Operations.AbsFactorExtendLeOne

@[expose] public section

/-!
# `factorExtend` stays within `[-1, 1]`

## Inputs
* `p` – number of factors
* `h` – number of dependent generators
* `q` – number of constraint generators
* `E` – exponent matrix
* `R` – constraint exponent matrix
* `a` – used factor values
* `k` – factor index

## Hypotheses
* `ha` – used factor values are within the unit interval

## Conclusion
* the extended factor value is within the unit interval
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.abs_factorExtend_le_one {p h q : ℕ} (E : Fin p → Fin h → ℕ)
    (R : Fin p → Fin q → ℕ) {a : Fin (ConPolyZono.usedFactors E R).card → ℝ}
    (ha : ∀ k, |a k| ≤ 1) (k : Fin p) :
    |ConPolyZono.factorExtend E R a k| ≤ 1 :=
  PolyZonotope.abs_factorExtend_le_one (ConPolyZono.appendE E R) ha k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
