import Mathlib.Analysis.CStarAlgebra.Matrix
import CORALean.Global.EuclideanNorm

/-!
# `‖G‖₂`, the induced `‖·‖₂` norm of a family of generators read as a linear map

Wetzlinger et al.'s TAC'23 `Prop. 9`'s `‖G_h^{(-)}‖₂` is not a plain vector's Euclidean norm:
`G_h^{(-)}` there is a matrix (`n × γ_h`), and `‖·‖₂` applied to a matrix is the induced operator
norm — the tight constant `sup {‖Mx‖₂ / ‖x‖₂ | x ≠ 0}` a Cauchy–Schwarz-style bound needs to be
sharp. Mathlib already carries exactly this: `Matrix.instL2OpNormedAddCommGroup` (scoped in
`Matrix.Norms.L2Operator`) reads a rectangular matrix's norm off the operator norm of the
`ContinuousLinearMap` it induces between `EuclideanSpace`s, and `Matrix.l2_opNorm_mulVec` is the
Cauchy–Schwarz bound itself. `genOpNorm₂` packages that at `Vec ℝ n`'s own generator-family
convention (`G j` is generator `j`, `Zonotope.G`'s own shape) rather than asking a caller to
transpose into a `Matrix` and open the scoped instance itself.

Read through `toEuclidean` exactly as `hausdorffDist₂`/`norm₂` are: the scoped instance is a
local elaboration device for `genOpNorm₂`'s own definition, not something a caller of the bound
below needs to open.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix
open scoped Matrix.Norms.L2Operator

variable {h n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Matrix.mulVec` against the transposed family is exactly the generators' linear
combination, entry by entry. -/
theorem aux_mulVec_genMat_eq (G : Fin h → Vec ℝ n) (v : Vec ℝ h) :
    (Matrix.of fun i j => G j i : Mat ℝ n h).mulVec v = ∑ j, v j • G j := by
  funext i
  simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_comm]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The induced `‖·‖₂` norm of a family of generators `G : Fin h → Vec ℝ n`, read as the `n × h`
matrix whose columns are the `G j` — Mathlib's operator norm between `EuclideanSpace`s. -/
noncomputable def genOpNorm₂ (G : Fin h → Vec ℝ n) : ℝ :=
  ‖(Matrix.of fun i j => G j i : Mat ℝ n h)‖

theorem genOpNorm₂_nonneg (G : Fin h → Vec ℝ n) : 0 ≤ genOpNorm₂ G := norm_nonneg _

/-- The Cauchy–Schwarz bound `genOpNorm₂` exists for: a linear combination of the generators
never exceeds their operator norm times the coefficient vector's own `‖·‖₂`. -/
theorem norm₂_sum_smul_le_genOpNorm₂_mul_norm₂ (G : Fin h → Vec ℝ n) (v : Vec ℝ h) :
    ‖∑ j, v j • G j‖₂ ≤ genOpNorm₂ G * ‖v‖₂ := by -- --- PROOF ---
  set M : Mat ℝ n h := Matrix.of fun i j => G j i with hM
  have hkey := Matrix.l2_opNorm_mulVec M (toEuclidean v)
  have hofLp : (toEuclidean v).ofLp = v := rfl
  -- `A *ᵥ x` for `x : EuclideanSpace` elaborates through `x.ofLp`, so unwrap it back to `v`
  have heq : (EuclideanSpace.equiv (Fin n) ℝ).symm (M *ᵥ toEuclidean v)
      = toEuclidean (M.mulVec v) := by
    show (EuclideanSpace.equiv (Fin n) ℝ).symm (M.mulVec (toEuclidean v).ofLp) = _
    rw [hofLp]; rfl
  rw [heq, norm_toEuclidean, aux_mulVec_genMat_eq] at hkey
  have hveq : ‖toEuclidean v‖ = ‖v‖₂ := norm_toEuclidean v
  rwa [hveq] at hkey

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
