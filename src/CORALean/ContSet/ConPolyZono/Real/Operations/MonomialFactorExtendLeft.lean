import CORALean.ContSet.ConPolyZono.Real.Operations.FactorExtend
import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorIdxLeft
import CORALean.ContSet.PolyZonotope.Real.Operations.FactorExtendFactorIdx

/-!
# The generator monomial read against an extended factor vector

What the reverse inclusion supplies.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same generator monomial read against an extended factor vector, which is
what the reverse inclusion supplies. -/
theorem ConPolyZono.monomial_factorExtend_left {p h s : ℕ} (E : Fin p → Fin h → ℕ)
    (EC : Fin p → Fin s → ℕ) (a : Fin (ConPolyZono.usedFactors E EC).card → ℝ) (i : Fin h) :
    PolyZonotope.monomial E (ConPolyZono.factorExtend E EC a) i
      = PolyZonotope.monomial
        (fun k i => E (ConPolyZono.factorIdx E EC k) i) a i := by -- --- PROOF ---
  have hmon := ConPolyZono.monomial_factorIdx_left E EC (ConPolyZono.factorExtend E EC a) i
  have hext : (fun k => ConPolyZono.factorExtend E EC a (ConPolyZono.factorIdx E EC k)) = a :=
    funext fun k => PolyZonotope.factorExtend_factorIdx (ConPolyZono.appendE E EC) a k
  rw [hext] at hmon
  exact hmon.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
