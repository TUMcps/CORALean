import CORALean.ContSet.PolyZonotope.Real.Operations.FactorExtendFactorIdx
import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialFactorIdx

/-!
# A monomial read against an extended factor vector

Split out of `Compact.lean` (issue #62): used again by
`Theorems/CompactFactorsExact.lean`, outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same monomial read against an extended factor vector: the extension
gives the dropped factors a value, and no monomial looks at it. -/
theorem PolyZonotope.monomial_factorExtend {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (a : Fin (PolyZonotope.usedFactors E).card → ℝ) (i : Fin h) :
    PolyZonotope.monomial E (PolyZonotope.factorExtend E a) i
      = PolyZonotope.monomial (fun k i => E (PolyZonotope.factorIdx E k) i)
        a i := by -- --- PROOF ---
  have hmon := PolyZonotope.monomial_factorIdx E (PolyZonotope.factorExtend E a) i
  have hext : (fun k => PolyZonotope.factorExtend E a (PolyZonotope.factorIdx E k)) = a :=
    funext fun k => PolyZonotope.factorExtend_factorIdx E a k
  rw [hext] at hmon
  exact hmon.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
