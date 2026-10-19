module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendERight
public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialFactorIdx

@[expose] public section

/-!
# The same at the constraint block, `appendE`'s right half
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same at the constraint block, `appendE`'s right half. -/
theorem ConPolyZono.monomial_factorIdx_right {p h q : ℕ} (E : Fin p → Fin h → ℕ)
    (R : Fin p → Fin q → ℕ) (a : Fin p → ℝ) (l : Fin q) : -- --- CONCL ---
    PolyZonotope.monomial (fun k l => R (ConPolyZono.factorIdx E R k) l)
        (fun k => a (ConPolyZono.factorIdx E R k)) l
      = PolyZonotope.monomial R a l :=
  calc PolyZonotope.monomial (fun k l => R (ConPolyZono.factorIdx E R k) l)
        (fun k => a (ConPolyZono.factorIdx E R k)) l
      = PolyZonotope.monomial
          (ConPolyZono.appendE (fun k i => E (ConPolyZono.factorIdx E R k) i)
            fun k l => R (ConPolyZono.factorIdx E R k) l)
          (fun k => a (ConPolyZono.factorIdx E R k)) (Fin.natAdd h l) :=
        (ConPolyZono.monomial_appendE_right _ _ _ l).symm
    _ = PolyZonotope.monomial (ConPolyZono.appendE E R) a (Fin.natAdd h l) :=
        PolyZonotope.monomial_factorIdx (ConPolyZono.appendE E R) a (Fin.natAdd h l)
    _ = PolyZonotope.monomial R a l := ConPolyZono.monomial_appendE_right E R a l

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
