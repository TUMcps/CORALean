module

public import CORALean.ContSet.ConPolyZono.Real.Operations.FactorExtend
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialFactorIdxLeft
public import CORALean.ContSet.PolyZonotope.Real.Operations.FactorExtendFactorIdx

@[expose] public section

/-!
# The generator monomial read against an extended factor vector

What the reverse inclusion supplies.

## Inputs
* `p` – number of factors
* `h` – number of dependent generators
* `q` – number of constraint generators
* `E` – exponent matrix
* `R` – constraint exponent matrix
* `a` – values of the used factors
* `i` – generator index

## Hypotheses
* none

## Conclusion
* extended and restricted factor vectors give the same generator monomial
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The same generator monomial read against an extended factor vector, which is
what the reverse inclusion supplies. -/
theorem ConPolyZono.monomial_factorExtend_left {p h q : ℕ} (E : Fin p → Fin h → ℕ)
    (R : Fin p → Fin q → ℕ) (a : Fin (ConPolyZono.usedFactors E R).card → ℝ)
    (i : Fin h) : -- --- CONCL ---
    PolyZonotope.monomial E (ConPolyZono.factorExtend E R a) i
      = PolyZonotope.monomial (fun k i => E (ConPolyZono.factorIdx E R k) i)
        a i := by -- --- PROOF ---
  have hmon := ConPolyZono.monomial_factorIdx_left E R (ConPolyZono.factorExtend E R a) i
  have hext : (fun k => ConPolyZono.factorExtend E R a (ConPolyZono.factorIdx E R k)) = a :=
    funext fun k => PolyZonotope.factorExtend_factorIdx (ConPolyZono.appendE E R) a k
  rw [hext] at hmon
  exact hmon.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
