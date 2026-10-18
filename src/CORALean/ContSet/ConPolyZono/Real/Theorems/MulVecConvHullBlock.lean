module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullA
public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullR
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecBlkDiag
public import CORALean.ContSet.ConPolyZono.Real.Operations.ProdBlkDiag
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# A copy's row of the convex hull

Row `i` of copy `j` of [1, Prop. 9]'s constraint matrix, at the hull's monomials, is the
operand's row `i` at copy `j`'s own factors: the copies sit block-diagonally and the weight
columns are zero on every copy's row.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A copy's constraint column names that copy's own monomial. -/
theorem ConPolyZono.aux_monomial_con {a p q : ℕ} (R : Fin p → Fin q → ℕ)
    (v : Fin (a * p + a) → ℝ) (j : Fin a) (l : Fin q) : -- --- STMT ---
    PolyZonotope.monomial (ConPolyZono.convHullR a R) v (Fin.castAdd a (finProdFinEquiv (j, l)))
      = PolyZonotope.monomial R
        (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k)))) l := by -- --- PROOF ---
  have h₁ : (∏ x : Fin (a * p), v (Fin.castAdd a x) ^ ConPolyZono.convHullR a R
      (Fin.castAdd a x) (Fin.castAdd a (finProdFinEquiv (j, l))))
      = ∏ k, v (Fin.castAdd a (finProdFinEquiv (j, k))) ^ R k l := by
    simp only [ConPolyZono.convHullR, Fin.append_left]
    exact ConPolyZono.prod_blkDiag R (fun x => v (Fin.castAdd a x)) j l
  -- the weight rows are zero throughout the copies' columns
  have h₂ : (∏ j' : Fin a, v (Fin.natAdd (a * p) j') ^ ConPolyZono.convHullR a R
      (Fin.natAdd (a * p) j') (Fin.castAdd a (finProdFinEquiv (j, l)))) = 1 := by
    simp [ConPolyZono.convHullR]
  rw [PolyZonotope.monomial, Fin.prod_univ_add, h₁, h₂, mul_one, PolyZonotope.monomial]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A copy's constraint row is the linear combination's, over that copy. -/
theorem ConPolyZono.mulVec_convHull_block {a p m q : ℕ} (A : Mat ℝ m q) (R : Fin p → Fin q → ℕ)
    (v : Fin (a * p + a) → ℝ) (j : Fin a) (i : Fin m) : -- --- STMT ---
    (ConPolyZono.convHullA a A *ᵥ PolyZonotope.monomial (ConPolyZono.convHullR a R) v)
        (Fin.castAdd 1 (finProdFinEquiv (j, i)))
      = (A *ᵥ PolyZonotope.monomial R
          (fun k => v (Fin.castAdd a (finProdFinEquiv (j, k))))) i := by -- --- PROOF ---
  show (∑ y, ConPolyZono.convHullA a A (Fin.castAdd 1 (finProdFinEquiv (j, i))) y
      * PolyZonotope.monomial (ConPolyZono.convHullR a R) v y)
    = ∑ l, A i l * PolyZonotope.monomial R _ l
  rw [Fin.sum_univ_add]
  -- the weight columns are zero on every copy's row
  simp only [ConPolyZono.convHullA, Fin.append_left, Fin.append_right, zero_mul,
    Finset.sum_const_zero, add_zero]
  rw [ConPolyZono.mulVec_blkDiag A
    (fun y => PolyZonotope.monomial (ConPolyZono.convHullR a R) v (Fin.castAdd a y)) j i]
  exact Finset.sum_congr rfl fun l _ => by rw [ConPolyZono.aux_monomial_con]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
