import CORALean.Global.CoeffNorm
import CORALean.Global.PiLpHolder

/-!
# A functional is bounded by the ellipsotope norm and the dual norm of its pull-back

The easy half of the dual form Eq. 21 of [1, Thm. 15 (accuracy)], [1, Thm. 17] and
[1, Thm. 19]: for `x` in the range of `H`, `zᵀ x ≤ ‖x‖_{E_q(H)} ‖Hᵀ z‖_{q*}`, where
`‖x‖_{E_q(H)} = min_{H β = x} ‖β‖_q` (`coeffNorm`). With `β` a minimizer,
`zᵀ x = zᵀ H β = (Hᵀ z)ᵀ β ≤ ‖Hᵀ z‖_{q*} ‖β‖_q` by Hölder.

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
      doi:10.1109/TAC.2025.3583624. arXiv:2404.11185.
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem dotProduct_le_coeffNorm_mul_norm (q q' : ℝ≥0∞) [Fact (1 ≤ q)] [q.HolderConjugate q']
    (H : Matrix (Fin n) (Fin l) ℝ) {x : Fin n → ℝ} (hx : ∃ β, H *ᵥ β = x) (z : Fin n → ℝ) :
    z ⬝ᵥ x ≤ coeffNorm ((Matrix.mulVecLin H) ∘ₗ
      (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap) x *
        ‖WithLp.toLp q' (z ᵥ* H)‖ := by -- --- PROOF ---
  set Hl := (Matrix.mulVecLin H) ∘ₗ (WithLp.linearEquiv q ℝ (Fin l → ℝ)).toLinearMap
  obtain ⟨β, hβ, hβn⟩ := exists_coeffNorm_eq Hl (x := x) (by
    obtain ⟨b, hb⟩ := hx
    exact ⟨WithLp.toLp q b, hb⟩)
  have hβ' : H *ᵥ WithLp.ofLp β = x := hβ
  calc z ⬝ᵥ x = ∑ i, (z ᵥ* H) i * WithLp.ofLp β i := by rw [← hβ', dotProduct_mulVec]; rfl
    _ ≤ ‖WithLp.toLp q' (z ᵥ* H)‖ * ‖WithLp.toLp q (WithLp.ofLp β)‖ :=
        piLp_sum_mul_le_norm_mul_norm q q' _ _
    _ = coeffNorm Hl x * ‖WithLp.toLp q' (z ᵥ* H)‖ := by
        rw [WithLp.toLp_ofLp, hβn, mul_comm]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
