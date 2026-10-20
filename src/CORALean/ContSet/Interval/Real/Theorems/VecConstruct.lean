module

public import CORALean.ContSet.Interval.Real.Operations.Vec
public import CORALean.ContSet.Interval.Real.Theorems.MemMat

@[expose] public section

/-!
# `Interval.vec` denotes the same matrices

A vector is in the stacked box exactly when it is the stacking of a matrix of the box: reshaping
is a bijection of the entries, and the box is a product of its entries. Hence every `representsa`
answer about the set of the vectorised interval is the answer for the matrix set.

## Inputs
* `A` – interval matrix

## Hypotheses
* none

## Conclusion
* the vectorised box is exactly the set of column-wise vectorisations
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The vectorised box is the image of the matrix box under stacking the columns. -/
theorem Interval.vec_construct (A : Interval (Mat ℝ m n)) : -- --- CONCL ---
    A.vec.construct = (fun M : Mat ℝ m n => fun k : Fin (n * m) =>
      M (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1) '' A.construct := by -- --- PROOF ---
  ext x
  constructor
  · intro hx
    refine ⟨Matrix.of fun i j => x (finProdFinEquiv (j, i)),
      Interval.mem_mat_iff.mpr fun i j => ?_, funext fun k => ?_⟩
    · have h : A.vec.inf (finProdFinEquiv (j, i)) ≤ x (finProdFinEquiv (j, i)) ∧
          x (finProdFinEquiv (j, i)) ≤ A.vec.sup (finProdFinEquiv (j, i)) := hx _
      simp only [Interval.vec, Equiv.symm_apply_apply] at h
      exact h
    · simp only [Matrix.of_apply, Prod.mk.eta, Equiv.apply_symm_apply]
  · rintro ⟨M, hM, rfl⟩ k
    exact Interval.mem_mat_iff.mp hM _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
