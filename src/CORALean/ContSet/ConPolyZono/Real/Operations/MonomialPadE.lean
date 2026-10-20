module

public import CORALean.ContSet.ConPolyZono.Real.Operations.PadE
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `padE` changes no monomial

The new factors sit at exponent zero, which is the only reason the block may
be carried through unchanged.

## Inputs
* `p` – number of factors
* `q` – number of columns
* `R` – exponent matrix
* `r` – number of added factors
* `a` – factor values
* `l` – column index

## Hypotheses
* none

## Conclusion
* padding the exponent matrix changes no monomial
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.monomial_padE {p q : ℕ} (R : Fin p → Fin q → ℕ) (r : ℕ)
    (a : Fin (p + r) → ℝ) (l : Fin q) :
    PolyZonotope.monomial (ConPolyZono.padE R r) a l
      = PolyZonotope.monomial R (fun k => a (Fin.castAdd r k)) l := by -- --- PROOF ---
  rw [PolyZonotope.monomial, PolyZonotope.monomial, Fin.prod_univ_add]
  -- the appended factors contribute a product of `1`q
  have hnew : (∏ k : Fin r, a (Fin.natAdd p k)
      ^ ConPolyZono.padE R r (Fin.natAdd p k) l) = 1 :=
    Finset.prod_eq_one fun k _ => by
      simp only [ConPolyZono.padE, PolyZonotope.padE, Fin.append_right, pow_zero]
  have hold : (∏ k : Fin p, a (Fin.castAdd r k)
      ^ ConPolyZono.padE R r (Fin.castAdd r k) l)
      = ∏ k, a (Fin.castAdd r k) ^ R k l :=
    Finset.prod_congr rfl fun k _ => by
      simp only [ConPolyZono.padE, PolyZonotope.padE, Fin.append_left]
  rw [hnew, hold, mul_one]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
