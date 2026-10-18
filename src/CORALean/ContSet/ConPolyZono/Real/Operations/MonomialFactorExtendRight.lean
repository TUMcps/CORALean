module

public import CORALean.ContSet.ConPolyZono.Real.Operations.FactorExtend
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorIdxRight
public import CORALean.ContSet.PolyZonotope.Real.Operations.FactorExtendFactorIdx

@[expose] public section

/-!
# The same at the constraint block
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same at the constraint block. -/
theorem ConPolyZono.monomial_factorExtend_right {p h q : ℕ} (E : Fin p → Fin h → ℕ)
    (R : Fin p → Fin q → ℕ) (a : Fin (ConPolyZono.usedFactors E R).card → ℝ)
    (l : Fin q) : -- --- STMT ---
    PolyZonotope.monomial R (ConPolyZono.factorExtend E R a) l
      = PolyZonotope.monomial (fun k l => R (ConPolyZono.factorIdx E R k) l)
        a l := by -- --- PROOF ---
  have hmon := ConPolyZono.monomial_factorIdx_right E R (ConPolyZono.factorExtend E R a) l
  have hext : (fun k => ConPolyZono.factorExtend E R a (ConPolyZono.factorIdx E R k)) = a :=
    funext fun k => PolyZonotope.factorExtend_factorIdx (ConPolyZono.appendE E R) a k
  rw [hext] at hmon
  exact hmon.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
