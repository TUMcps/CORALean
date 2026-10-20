module

public import CORALean.ContSet.PolyZonotope.Real.Operations.ExtG
public import CORALean.ContSet.PolyZonotope.Real.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Real.Operations.QuadMap
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# A point of the set as a single sum

The center becomes generator zero at the all-zero exponent column, so the whole
point is one sum over the extended index. Stated pointwise rather than as a set
equality because the constrained representation needs it at a *fixed* factor
vector, which is also why it carries no `aux_` prefix.

## Inputs
* `pZ` – polynomial zonotope
* `a` – factor values

## Hypotheses
* none

## Conclusion
* the extended sum is the center plus the generator sum
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open PolyZonotope

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the set as one sum, the center being generator zero at the
all-zero exponent column. -/
theorem PolyZonotope.sum_ext_eq_point (pZ : PolyZonotope α) (a : Fin pZ.p → ℝ) : -- --- CONCL ---
    ∑ l, extM pZ a l • extG pZ l = pZ.c + ∑ i, monomial pZ.E a i • pZ.G i := by -- --- PROOF ---
  have h0 : extM pZ a 0 = 1 := by
    show ∏ k, a k ^ PolyZonotope.extE pZ k 0 = 1
    exact Finset.prod_eq_one fun k _ => by
      simp only [PolyZonotope.extE, Fin.cons_zero, pow_zero]
  have hG0 : extG pZ 0 = pZ.c := by
    simp only [PolyZonotope.extG, Fin.cons_zero]
  -- every other column is an original generator, shifted by the one the center took
  have hsucc : ∀ i : Fin pZ.h,
      extM pZ a i.succ • extG pZ i.succ = monomial pZ.E a i • pZ.G i := by
    intro i
    have hm : extM pZ a i.succ = monomial pZ.E a i := by
      show ∏ k, a k ^ PolyZonotope.extE pZ k i.succ = ∏ k, a k ^ pZ.E k i
      exact Finset.prod_congr rfl fun k _ => by
        simp only [PolyZonotope.extE, Fin.cons_succ]
    have hg : extG pZ i.succ = pZ.G i := by
      simp only [PolyZonotope.extG, Fin.cons_succ]
    rw [hm, hg]
  rw [Fin.sum_univ_succ, h0, hG0, one_smul]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => hsucc i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
