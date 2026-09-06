import CORALean.ContSet.ConPolyZono.Real.Operations.FactorExtend
import CORALean.ContSet.PolyZonotope.Real.Operations.AbsFactorExtendLeOne

/-!
# `factorExtend` stays within `[-1, 1]`
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

theorem ConPolyZono.abs_factorExtend_le_one {p h s : ℕ} (E : Fin p → Fin h → ℕ)
    (EC : Fin p → Fin s → ℕ) {a : Fin (ConPolyZono.usedFactors E EC).card → ℝ}
    (ha : ∀ k, |a k| ≤ 1) (k : Fin p) :
    |ConPolyZono.factorExtend E EC a k| ≤ 1 :=
  PolyZonotope.abs_factorExtend_le_one (ConPolyZono.appendE E EC) ha k

end CORALean.Real
