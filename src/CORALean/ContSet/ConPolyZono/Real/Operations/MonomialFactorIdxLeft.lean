import CORALean.ContSet.ConPolyZono.Real.Operations.FactorIdx
import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendELeft
import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialFactorIdx

/-!
# A generator monomial reads the kept factors and no others

It is a monomial of `appendE`'s left half, and `monomial_factorIdx` holds of
the whole.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

/-- A generator monomial reads the kept factors and no others: it is a monomial
of `appendE`'s left half, and `monomial_factorIdx` holds of the whole. -/
theorem ConPolyZono.monomial_factorIdx_left {p h s : ℕ} (E : Fin p → Fin h → ℕ)
    (EC : Fin p → Fin s → ℕ) (a : Fin p → ℝ) (i : Fin h) :
    PolyZonotope.monomial (fun k i => E (ConPolyZono.factorIdx E EC k) i)
        (fun k => a (ConPolyZono.factorIdx E EC k)) i
      = PolyZonotope.monomial E a i :=
  calc PolyZonotope.monomial (fun k i => E (ConPolyZono.factorIdx E EC k) i)
        (fun k => a (ConPolyZono.factorIdx E EC k)) i
      = PolyZonotope.monomial
          (ConPolyZono.appendE (fun k i => E (ConPolyZono.factorIdx E EC k) i)
            fun k l => EC (ConPolyZono.factorIdx E EC k) l)
          (fun k => a (ConPolyZono.factorIdx E EC k)) (Fin.castAdd s i) :=
        (ConPolyZono.monomial_appendE_left _ _ _ i).symm
    _ = PolyZonotope.monomial (ConPolyZono.appendE E EC) a (Fin.castAdd s i) :=
        PolyZonotope.monomial_factorIdx (ConPolyZono.appendE E EC) a (Fin.castAdd s i)
    _ = PolyZonotope.monomial E a i := ConPolyZono.monomial_appendE_left E EC a i

end CORALean.Real
