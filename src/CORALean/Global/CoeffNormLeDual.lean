module

public import CORALean.Global.CoeffNorm
public import CORALean.Global.LinearRelaxationDual

@[expose] public section

/-!
# The ellipsotope norm is attained by a dual vector

The dual form of the ellipsotope norm that [1, Thm. 17] and [1, Thm. 19] bound the radius by
(the inner maximum of Eq. 21): for `x = H β₀` in the range of `H`, some `z` with
`‖Hᵀ z‖_{q*} ≤ 1` has `min_{H β = x} ‖β‖_q ≤ zᵀ x`. It is `lr_exists_dual` at a single
column: `LR_q(x, H)` is the minimum of `‖β‖_q` over `H β = x`, and the dual certificate is a
vector `z` with `‖Hᵀ z‖_{q*} ≤ 1` and `zᵀ x ≥ LR_q(x, H)`.

## Inputs
* `q` – exponent of the coefficient norm
* `q'` – conjugate exponent
* `H` – coefficient matrix
* `x` – point in the range of the matrix

## Hypotheses
* `hx` – the point is attained by some coefficient vector

## Conclusion
* a dual vector of unit dual norm bounds the point's coefficient norm by its pairing with the point

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped ENNReal
open Matrix

variable {n l : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A `q`-norm depends only on the absolute values of the entries. -/
private theorem aux_cnd_norm_congr_abs (q : ℝ≥0∞) [Fact (1 ≤ q)] (a b : Fin l → ℝ)
    (h : ∀ i, |a i| = |b i|) : -- --- CONCL ---
    ‖WithLp.toLp q a‖ = ‖WithLp.toLp q b‖ := by -- --- PROOF ---
  by_cases hq : q = ∞
  · subst hq
    simp [PiLp.norm_eq_ciSup, Real.norm_eq_abs, h]
  · have hq0 : 0 < q.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
    simp [PiLp.norm_eq_sum hq0, Real.norm_eq_abs, h]


-- =======================================  MAIN THEOREM  ======================================= --

theorem exists_dual_coeffNorm_le (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q']
    (H : Matrix (Fin n) (Fin l) ℝ) {x : Fin n → ℝ} (hx : ∃ β, H *ᵥ β = x) : -- --- CONCL ---
    ∃ z : Fin n → ℝ, ‖WithLp.toLp q' (z ᵥ* H)‖ ≤ 1 ∧
      coeffNorm ((Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap) x ≤
        z ⬝ᵥ x := by -- --- PROOF ---
  set Hl := (Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap
  obtain ⟨β₀, hβ₀⟩ := hx
  set Gx : Matrix (Fin n) (Fin 1) ℝ := Matrix.of fun k _ => x k
  obtain ⟨LR, ⟨⟨X, hX, hXLR⟩, -⟩, Y, hY, hLRY⟩ := lr_exists_dual q q' Gx H
    ⟨Matrix.of fun i _ => β₀ i, by ext k j; simp [Gx, ← hβ₀, mulVec, dotProduct, mul_apply]⟩
  set z : Fin n → ℝ := fun k => Y k 0
  refine ⟨z, ?_, ?_⟩
  · -- `‖Hᵀ Y‖_{L⊤∞,q*}` is `‖Hᵀ z‖_{q*}` at one column
    refine le_trans ?_ hY
    haveI : Fact (1 ≤ q') := ⟨ENNReal.HolderConjugate.one_le q' q⟩
    refine le_of_eq (aux_cnd_norm_congr_abs q' _ _ fun i => ?_)
    rw [abs_of_nonneg (Real.iSup_nonneg fun j => abs_nonneg _)]
    rw [show (⨆ j : Fin 1, |(Hᵀ * Y) i j|) = |(Hᵀ * Y) i 0| from ciSup_unique]
    simp [z, vecMul, dotProduct, mul_apply, mul_comm]
  · -- `coeffNorm x ≤ ‖X₀‖_q = LR ≤ tr(xᵀ Y) = zᵀ x`
    set β : Fin l → ℝ := fun i => X i 0
    have hβ : Hl (WithLp.toLp q β) = x := by
      funext k
      have := congrFun (congrFun hX k) 0
      simpa [Hl, β, Gx, mulVec, dotProduct, mul_apply] using this
    calc coeffNorm Hl x ≤ ‖WithLp.toLp q β‖ := hβ ▸ coeffNorm_le Hl _
      _ = LR := by
          rw [hXLR]
          exact aux_cnd_norm_congr_abs q _ _ fun i => (abs_abs _).symm.trans (by
            simp [β])
      _ ≤ trace (Gxᵀ * Y) := hLRY
      _ = z ⬝ᵥ x := by
          simp [trace, Gx, z, mul_apply, dotProduct, mul_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
