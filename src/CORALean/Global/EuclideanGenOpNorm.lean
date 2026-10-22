module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# `‖G‖₂`, the induced `‖·‖₂` norm of a family of generators read as a linear map

Wetzlinger et al.'s TAC'23 `Prop. 9`'s `‖G_h^{(-)}‖₂` is the induced operator norm of a matrix
(`n × γ_h`), `sup {‖Mx‖₂ / ‖x‖₂ | x ≠ 0}`, the tight constant a Cauchy–Schwarz-style bound needs.
Mathlib carries it: `Matrix.instL2OpNormedAddCommGroup` (scoped in `Matrix.Norms.L2Operator`) reads
a rectangular matrix's norm off the operator norm of the `ContinuousLinearMap` between
`EuclideanSpace`s, and `Matrix.l2_opNorm_mulVec` is the bound itself. `genOpNorm₂` packages that at
`Vec ℝ n`'s generator-family convention (`G j` is generator `j`, as `Zonotope.G`), read through
`toEuclidean` as `hausdorffDist₂`/`norm₂` are, so a caller need not open the scoped instance.

## Inputs
* `G` – family of generators

## Output
* the induced Euclidean operator norm of the generator matrix
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


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

/-- The induced Euclidean norm of a generator family is nonnegative. -/
theorem genOpNorm₂_nonneg (G : Fin h → Vec ℝ n) : 0 ≤ genOpNorm₂ G := norm_nonneg _

/-- The Cauchy–Schwarz bound `genOpNorm₂` exists for: a linear combination of the generators
never exceeds their operator norm times the coefficient vector's own `‖·‖₂`. -/
theorem norm₂_sum_smul_le_genOpNorm₂_mul_norm₂ (G : Fin h → Vec ℝ n)
    (v : Vec ℝ h) : -- --- CONCL ---
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


/-- And the bound in the other direction, which is what an error term shrinking to `0` needs: the
generators' own Euclidean lengths, summed, dominate the operator norm. Loose by up to `√h` against
the tight constant, and enough wherever the quantity bounded is an asymptotic one. -/
theorem genOpNorm₂_le_sum_norm₂ (G : Fin h → Vec ℝ n) : -- --- CONCL ---
    genOpNorm₂ G ≤ ∑ j, ‖G j‖₂ := by -- --- PROOF ---
  have hnn : (0:ℝ) ≤ ∑ j, ‖G j‖₂ := Finset.sum_nonneg fun j _ => norm₂_nonneg _
  rw [genOpNorm₂, Matrix.l2_opNorm_def]
  have key : ∀ T : EuclideanSpace ℝ (Fin h) →L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ x, ‖T x‖ ≤ (∑ j, ‖G j‖₂) * ‖x‖) → ‖T‖ ≤ ∑ j, ‖G j‖₂ :=
    fun T hT => T.opNorm_le_bound hnn hT
  refine key _ ?_
  intro x
  -- the induced map at `x` is the generators' combination, read back through `toEuclidean`
  change ‖toEuclidean ((Matrix.of fun i j => G j i : Mat ℝ n h).mulVec (WithLp.ofLp x))‖ ≤ _
  have hxn : ‖x‖ = ‖(WithLp.ofLp x : Vec ℝ h)‖₂ := norm_toEuclidean _
  rw [norm_toEuclidean, hxn, aux_mulVec_genMat_eq]
  calc ‖∑ j, (WithLp.ofLp x : Vec ℝ h) j • G j‖₂
      ≤ ∑ j, ‖(WithLp.ofLp x : Vec ℝ h) j • G j‖₂ := norm₂_sum_le _ _
    _ = ∑ j, |(WithLp.ofLp x : Vec ℝ h) j| * ‖G j‖₂ :=
        Finset.sum_congr rfl fun j _ => norm₂_smul _ _
    _ ≤ ∑ j, ‖(WithLp.ofLp x : Vec ℝ h)‖₂ * ‖G j‖₂ :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (abs_le_norm₂ _ j) (norm₂_nonneg _)
    _ = (∑ j, ‖G j‖₂) * ‖(WithLp.ofLp x : Vec ℝ h)‖₂ := by rw [← Finset.mul_sum, mul_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
