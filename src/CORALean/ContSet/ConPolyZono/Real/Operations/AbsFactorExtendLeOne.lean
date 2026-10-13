module

public import CORALean.ContSet.ConPolyZono.Real.Operations.FactorExtend
public import CORALean.ContSet.PolyZonotope.Real.Operations.AbsFactorExtendLeOne

@[expose] public section

/-!
# `factorExtend` stays within `[-1, 1]`
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.abs_factorExtend_le_one {p h s : ℕ} (E : Fin p → Fin h → ℕ)
    (EC : Fin p → Fin s → ℕ) {a : Fin (ConPolyZono.usedFactors E EC).card → ℝ}
    (ha : ∀ k, |a k| ≤ 1) (k : Fin p) :
    |ConPolyZono.factorExtend E EC a k| ≤ 1 :=
  PolyZonotope.abs_factorExtend_le_one (ConPolyZono.appendE E EC) ha k

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
