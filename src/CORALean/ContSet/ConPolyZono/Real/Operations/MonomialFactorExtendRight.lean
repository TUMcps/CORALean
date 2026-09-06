import CORALean.ContSet.ConPolyZono.Real.Operations.FactorExtend
import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorIdxRight
import CORALean.ContSet.PolyZonotope.Real.Operations.FactorExtendFactorIdx

/-!
# The same at the constraint block
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same at the constraint block. -/
theorem ConPolyZono.monomial_factorExtend_right {p h s : ℕ} (E : Fin p → Fin h → ℕ)
    (EC : Fin p → Fin s → ℕ) (a : Fin (ConPolyZono.usedFactors E EC).card → ℝ) (l : Fin s) :
    PolyZonotope.monomial EC (ConPolyZono.factorExtend E EC a) l
      = PolyZonotope.monomial
        (fun k l => EC (ConPolyZono.factorIdx E EC k) l) a l := by -- --- PROOF ---
  have hmon := ConPolyZono.monomial_factorIdx_right E EC (ConPolyZono.factorExtend E EC a) l
  have hext : (fun k => ConPolyZono.factorExtend E EC a (ConPolyZono.factorIdx E EC k)) = a :=
    funext fun k => PolyZonotope.factorExtend_factorIdx (ConPolyZono.appendE E EC) a k
  rw [hext] at hmon
  exact hmon.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
