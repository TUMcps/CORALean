module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# (A.7) and (A.8) have the same solutions

[1, Sec. 4.2 (choice of j)]: with `Q` the upper-left `(n_g + n_c) × (n_g + n_c)` block of (A.7),
"(A.7) is equivalent to" (A.8), `[I, Q⁻¹e_j; e_jᵀ, 0][ŵ; μ̂] = [0; r_j]`, `e_j` now in `ℝ^{n_g+n_c}`
and `ŵ` stacking `d̂` and the multipliers of `Ad = 0`. The first block row of (A.7) is
`Qŵ + μ̂e_j = 0`, and multiplying it by `Q⁻¹`, or back by `Q`, gives (A.8)'s `ŵ + μ̂Q⁻¹e_j = 0`. The
last row is the same in both. This is why one factorization of `Q` serves every `j`.

## Inputs
* `m` – system size
* `Q` – upper-left block
* `e` – coupling vector
* `w` – unknown vector
* `μ` – multiplier
* `r` – pivot value

## Hypotheses
* `hQ` – the block is invertible

## Conclusion
* the two linear systems have the same solutions

## References

* [1] [J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica,
      2016.](../../../../../../references/2016/scott-automatica-constrained-zonotopes.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2 (choice of j)]: at invertible `Q`, the two systems in `(ŵ, μ̂)` agree. -/
theorem ConZonotope.hausdorffEstimate_reduced_iff {m : ℕ} (Q : Mat ℝ m m) (hQ : IsUnit Q.det)
    (e w : Vec ℝ m) (μ r : ℝ) : -- --- CONCL ---
    (Q *ᵥ w + μ • e = 0 ∧ e ⬝ᵥ w = r)
      ↔ (w + μ • (Q⁻¹ *ᵥ e) = 0 ∧ e ⬝ᵥ w = r) := by -- --- PROOF ---
  refine and_congr_left fun _ => ?_
  constructor
  · intro h
    -- multiply the first block row by `Q⁻¹`
    have := congrArg (Q⁻¹ *ᵥ ·) h
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul Q hQ, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact this
  · intro h
    -- and back by `Q`
    have := congrArg (Q *ᵥ ·) h
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv Q hQ, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
