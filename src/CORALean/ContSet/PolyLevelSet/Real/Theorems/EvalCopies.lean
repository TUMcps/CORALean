module

public import CORALean.ContSet.PolyLevelSet.Real.Operations.Copies
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `PolyLevelSet.copies`'s rows

Row `i` of copy `j` is `P`'s row `i` at the `j`-th block of variables: the other blocks meet it at
coefficient zero and at exponent zero (`mulVec_repBlockDiag`, `prod_repBlockDiag`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Block `j`'s row of `repBlockDiag 0 a A` pairs with block `j`'s entries alone. -/
theorem PolyLevelSet.aux_mulVec_repBlockDiag {a m q : ℕ} (A : Mat ℝ m q) (u : Fin (a * q) → ℝ)
    (j : Fin a) (i : Fin m) :
    (∑ y, repBlockDiag 0 a A (finProdFinEquiv (j, i)) y * u y)
      = ∑ l, A i l * u (finProdFinEquiv (j, l)) := by -- --- PROOF ---
  rw [sum_rep (fun y => repBlockDiag 0 a A (finProdFinEquiv (j, i)) y * u y)]
  refine (Finset.sum_eq_single j (fun j' _ hj' => ?_)
    (fun h => absurd (Finset.mem_univ j) h)).trans ?_
  -- every other block meets this row at zero
  · exact Finset.sum_eq_zero fun l _ => by simp [repBlockDiag, Ne.symm hj']
  · exact Finset.sum_congr rfl fun l _ => by simp [repBlockDiag]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Copy `j`'s row `i` is `P`'s row `i` at block `j`. -/
theorem PolyLevelSet.eval_copies (P : PolyLevelSet n) (a : ℕ) (x : Vec ℝ (a * n)) (j : Fin a)
    (i : Fin P.m) :
    (P.copies a).eval x (finProdFinEquiv (j, i))
      = P.eval (fun k => x (finProdFinEquiv (j, k))) i := by -- --- PROOF ---
  show (∑ y, repBlockDiag 0 a P.A (finProdFinEquiv (j, i)) y
      * PolyZonotope.monomial (repBlockDiag 0 a P.R) x y) - repVec a P.b (finProdFinEquiv (j, i))
    = (∑ l, P.A i l * PolyZonotope.monomial P.R (fun k => x (finProdFinEquiv (j, k))) l) - P.b i
  rw [PolyLevelSet.aux_mulVec_repBlockDiag]
  simp only [repVec, Equiv.symm_apply_apply, PolyZonotope.monomial, prod_repBlockDiag]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
