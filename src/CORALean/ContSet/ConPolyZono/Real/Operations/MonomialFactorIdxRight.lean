import CORALean.ContSet.ConPolyZono.Real.Operations.FactorIdx
import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendERight
import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialFactorIdx

/-!
# The same at the constraint block, `appendE`'s right half
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

/-- The same at the constraint block, `appendE`'s right half. -/
theorem ConPolyZono.monomial_factorIdx_right {p h s : ℕ} (E : Fin p → Fin h → ℕ)
    (EC : Fin p → Fin s → ℕ) (a : Fin p → ℝ) (l : Fin s) :
    PolyZonotope.monomial (fun k l => EC (ConPolyZono.factorIdx E EC k) l)
        (fun k => a (ConPolyZono.factorIdx E EC k)) l
      = PolyZonotope.monomial EC a l :=
  calc PolyZonotope.monomial (fun k l => EC (ConPolyZono.factorIdx E EC k) l)
        (fun k => a (ConPolyZono.factorIdx E EC k)) l
      = PolyZonotope.monomial
          (ConPolyZono.appendE (fun k i => E (ConPolyZono.factorIdx E EC k) i)
            fun k l => EC (ConPolyZono.factorIdx E EC k) l)
          (fun k => a (ConPolyZono.factorIdx E EC k)) (Fin.natAdd h l) :=
        (ConPolyZono.monomial_appendE_right _ _ _ l).symm
    _ = PolyZonotope.monomial (ConPolyZono.appendE E EC) a (Fin.natAdd h l) :=
        PolyZonotope.monomial_factorIdx (ConPolyZono.appendE E EC) a (Fin.natAdd h l)
    _ = PolyZonotope.monomial EC a l := ConPolyZono.monomial_appendE_right E EC a l

end CORALean.Real
