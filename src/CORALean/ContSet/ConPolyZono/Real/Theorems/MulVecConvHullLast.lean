module

public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullA
public import CORALean.ContSet.ConPolyZono.Real.Operations.ConvHullR
public import CORALean.ContSet.ConPolyZono.Real.Operations.MulVecBlkDiag
public import CORALean.ContSet.ConPolyZono.Real.Operations.ProdBlkDiag
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The weight row of the convex hull

The last row of [1, Prop. 9]'s constraint matrix, at the hull's monomials, is the sum of the
weight factors: its `1` entries meet the weight columns alone, each of which names its own
weight factor.

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

/-- A weight column names its own weight factor. -/
theorem ConPolyZono.aux_monomial_lam {a p q : ℕ} (R : Fin p → Fin q → ℕ)
    (v : Fin (a * p + a) → ℝ) (j : Fin a) :
    PolyZonotope.monomial (ConPolyZono.convHullR a R) v (Fin.natAdd (a * q) j)
      = v (Fin.natAdd (a * p) j) := by -- --- PROOF ---
  have h₁ : (∏ x : Fin (a * p), v (Fin.castAdd a x) ^ ConPolyZono.convHullR a R
      (Fin.castAdd a x) (Fin.natAdd (a * q) j)) = 1 := by
    simp [ConPolyZono.convHullR]
  -- and only `j`'s own weight row carries a power here
  have h₂ : (∏ j' : Fin a, v (Fin.natAdd (a * p) j') ^ ConPolyZono.convHullR a R
      (Fin.natAdd (a * p) j') (Fin.natAdd (a * q) j)) = v (Fin.natAdd (a * p) j) := by
    simp only [ConPolyZono.convHullR, Fin.append_right]
    refine (Finset.prod_eq_single j (fun j' _ hj' => ?_)
      (fun hj => absurd (Finset.mem_univ j) hj)).trans ?_
    · simp [ConPolyZono.unitCol, Ne.symm hj']
    · simp [ConPolyZono.unitCol]
  rw [PolyZonotope.monomial, Fin.prod_univ_add, h₁, h₂, one_mul]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The last row adds the weight factors and nothing else. -/
theorem ConPolyZono.mulVec_convHull_last {a p m q : ℕ} (A : Mat ℝ m q) (R : Fin p → Fin q → ℕ)
    (v : Fin (a * p + a) → ℝ) : -- --- STMT ---
    (ConPolyZono.convHullA a A *ᵥ PolyZonotope.monomial (ConPolyZono.convHullR a R) v)
        (Fin.natAdd (a * m) (0 : Fin 1))
      = ∑ j, v (Fin.natAdd (a * p) j) := by -- --- PROOF ---
  show (∑ y, ConPolyZono.convHullA a A (Fin.natAdd (a * m) (0 : Fin 1)) y
      * PolyZonotope.monomial (ConPolyZono.convHullR a R) v y) = _
  rw [Fin.sum_univ_add]
  -- the copies' columns are zero on this row
  simp only [ConPolyZono.convHullA, Fin.append_left, Fin.append_right, zero_mul,
    Finset.sum_const_zero, zero_add, one_mul]
  exact Finset.sum_congr rfl fun j _ => ConPolyZono.aux_monomial_lam R v j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
