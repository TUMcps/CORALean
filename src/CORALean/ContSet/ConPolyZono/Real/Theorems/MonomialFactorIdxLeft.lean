module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialAppendELeft
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MonomialFactorIdx

@[expose] public section

/-!
# A generator monomial reads the kept factors and no others

It is a monomial of `appendE`'s left half, and `monomial_factorIdx` holds of
the whole.

## Inputs
* `p` – number of factors
* `h` – number of dependent generators
* `q` – number of constraint generators
* `E` – exponent matrix
* `R` – constraint exponent matrix
* `a` – factor values
* `i` – generator index

## Hypotheses
* none

## Conclusion
* restricting to the kept factors leaves the generator monomial unchanged
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- A generator monomial reads the kept factors and no others: it is a monomial
of `appendE`'s left half, and `monomial_factorIdx` holds of the whole. -/
theorem ConPolyZono.monomial_factorIdx_left {p h q : ℕ} (E : Fin p → Fin h → ℕ)
    (R : Fin p → Fin q → ℕ) (a : Fin p → ℝ) (i : Fin h) :
    PolyZonotope.monomial (fun k i => E (ConPolyZono.factorIdx E R k) i)
        (fun k => a (ConPolyZono.factorIdx E R k)) i
      = PolyZonotope.monomial E a i :=
  calc PolyZonotope.monomial (fun k i => E (ConPolyZono.factorIdx E R k) i)
        (fun k => a (ConPolyZono.factorIdx E R k)) i
      = PolyZonotope.monomial
          (ConPolyZono.appendE (fun k i => E (ConPolyZono.factorIdx E R k) i)
            fun k l => R (ConPolyZono.factorIdx E R k) l)
          (fun k => a (ConPolyZono.factorIdx E R k)) (Fin.castAdd q i) :=
        (ConPolyZono.monomial_appendE_left _ _ _ i).symm
    _ = PolyZonotope.monomial (ConPolyZono.appendE E R) a (Fin.castAdd q i) :=
        PolyZonotope.monomial_factorIdx (ConPolyZono.appendE E R) a (Fin.castAdd q i)
    _ = PolyZonotope.monomial E a i := ConPolyZono.monomial_appendE_left E R a i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
