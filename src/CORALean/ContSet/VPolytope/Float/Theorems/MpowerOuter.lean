module

public import CORALean.ContSet.VPolytope.Float.Operations.Mpower
public import CORALean.ContSet.VPolytope.Float.Theorems.MatMulOuter
public import CORALean.ContSet.VPolytope.Real.Theorems.ConstructPoint

@[expose] public section

/-!
# `VPolytope.mpower` contains the matrix powers

The zeroth power is the identity, the first is the polytope, and each next one is the rounded
product of the previous power with the polytope, which `VPolytope.matMul_outer` encloses.

## Inputs
* `P` – matrix polytope
* `M` – member of `P`
* `k` – exponent

## Hypotheses
* `hM` – `M` lies in `P`

## Conclusion
* `M ^ k` lies in the `k`-th power
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise InflatedContSet FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.mpower_outer (P : VPolytope (Mat 𝕋 n n)) {M : Mat ℝ n n}
    (hM : M ∈ InflatedContSet.construct P) (k : ℕ) : -- --- CONCL ---
    M ^ k ∈ InflatedContSet.construct (P.mpower k) := by -- --- PROOF ---
  rcases k with _ | k
  · -- the identity is the single vertex `1`, with a zero error box
    have h1 : toRealMat (diagonalBlock fun _ : Fin n => (one : 𝕋)) = (1 : Mat ℝ n n) := by
      funext i j
      rw [toRealMat, toReal_diagonalBlock]
      simp [toRealVec, toReal_one, Matrix.one_apply, Matrix.diagonal_apply]
    have hv : toRealMat (diagonalBlock fun _ : Fin n => (one : 𝕋)) ∈
        (Real.VPolytope.point (toRealMat (diagonalBlock fun _ : Fin n => (one : 𝕋)))).construct
        := by
      rw [Real.VPolytope.construct_point]
      rfl
    -- the vertex is the identity, and the zero box holds `0`
    refine ⟨1, ?_, 0, ?_, add_zero 1⟩
    · rw [← h1]
      exact hv
    · exact Interval.mem_mat_iff.mpr fun i j => by
        show toReal (zero : 𝕋) ≤ 0 ∧ 0 ≤ toReal (zero : 𝕋)
        rw [toReal_zero]
        exact ⟨le_rfl, le_rfl⟩
  · induction k with
    | zero => rw [zero_add, pow_one]; exact hM
    | succ k ih =>
      rw [pow_succ]
      exact VPolytope.matMul_outer _ P ih hM

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
