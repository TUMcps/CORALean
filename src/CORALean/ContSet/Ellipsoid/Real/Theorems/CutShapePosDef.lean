import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
import CORALean.ContSet.Ellipsoid.Real.Operations.CutShape
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The cut ellipsoid's shape matrix is positive definite

[1, Eq. 16]'s matrix `a(I − κ c cᵀ)` is symmetric, and its quadratic form is
`a(xᵀx − κ (cᵀx)²) ≥ a(1 − κ) xᵀx > 0` for `x ≠ 0`, by Cauchy-Schwarz `(cᵀx)² ≤ xᵀx` for a unit
`c`, with `a = n(1 − γ²)/(n − 1) > 0` and `κ = (1 − nγ²)/(1 − γ²) ∈ [0, 1)`. So it is the
shape matrix of an ellipsoid (`Ellipsoid.ofShape`) for `n ≥ 2`, `0 < γ`, `nγ² < 1`.

## References

* [1] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Ellipsoid.aux_quad (a κ : ℝ) (c x : Vec ℝ n) :
    x ⬝ᵥ ((a • (1 - κ • vecMulVec c c : Mat ℝ n n)) *ᵥ x)
      = a * (x ⬝ᵥ x - κ * (c ⬝ᵥ x) ^ 2) := by -- --- PROOF ---
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec]
  simp only [dotProduct_smul, dotProduct_sub, smul_eq_mul, op_smul_eq_smul]
  rw [dotProduct_comm x c]
  ring

theorem Ellipsoid.aux_cs (c x : Vec ℝ n) (hc : c ⬝ᵥ c = 1) : (c ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ x := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c x
  have h1 : ∑ i, c i ^ 2 = 1 := by simpa [dotProduct, sq] using hc
  rw [h1, one_mul] at this
  simpa [dotProduct, sq] using this


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 16]'s shape matrix is positive definite. -/
theorem Ellipsoid.cutShape_posDef {c : Vec ℝ n} (hc : c ⬝ᵥ c = 1) {γ : ℝ}
    (hn : 2 ≤ n) (hγ : 0 < γ) (hγn : (n : ℝ) * γ ^ 2 < 1) :
    (Ellipsoid.cutShape n c γ).PosDef := by -- --- PROOF ---
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 0 < 1 - γ ^ 2 := by nlinarith [sq_nonneg γ]
  have h2 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have ha0 : 0 < (n : ℝ) * (1 - γ ^ 2) / ((n : ℝ) - 1) := by positivity
  have hκ1 : (1 - (n : ℝ) * γ ^ 2) / (1 - γ ^ 2) < 1 := by
    rw [div_lt_one h1]; nlinarith [sq_pos_of_pos hγ]
  have hκ0 : 0 ≤ (1 - (n : ℝ) * γ ^ 2) / (1 - γ ^ 2) := div_nonneg (by linarith) h1.le
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · -- symmetric
    unfold Ellipsoid.cutShape IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial, transpose_smul, transpose_sub, transpose_one,
      transpose_smul, transpose_vecMulVec]
  · intro x hx
    simp only [star_trivial]
    unfold Ellipsoid.cutShape
    rw [Ellipsoid.aux_quad]
    have hcs := Ellipsoid.aux_cs c x hc
    have hxx : 0 < x ⬝ᵥ x :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (x i))
        (Ne.symm ((not_congr dotProduct_self_eq_zero).2 hx))
    apply mul_pos ha0
    nlinarith [mul_nonneg hκ0 (sub_nonneg.2 hcs)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
