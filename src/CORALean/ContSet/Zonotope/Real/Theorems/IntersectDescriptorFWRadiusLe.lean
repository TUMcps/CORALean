module

public import CORALean.ContSet.Zonotope.Real.Operations.IntersectDescriptor
public import CORALean.ContSet.Zonotope.Real.Theorems.FWRadiusSqEqTrace
public import CORALean.Global.TraceGainLe
public import CORALean.Global.SumVecMulVecCol
public import CORALean.Global.VecMulVecMulVecSelf
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The Kalman correction matrix minimizes the F_W-radius

[1, Thm. 2]: among all correction matrices `Λ`, the intersection zonotope `⟨p̂₊(Λ), Ĥ₊(Λ)⟩` of Eq. 7
of [1, Thm. 1] has the least F_W-radius at `Λ* = L S⁻¹` Eq. 12 of [1, Thm. 2], `L = R̄ Cᵀ` Eq. 13 of
[1, Thm. 2], `S = C R̄ Cᵀ + Q_v` Eq. 14 of [1, Thm. 2], `R̄ = T(A P̄ Aᵀ + Q_w)Tᵀ + N Q_v Nᵀ` Eq. 15
of [1, Thm. 2], with `P̄ = H̄ H̄ᵀ`, `Q_w = D Dᵀ`, `Q_v = F Fᵀ`. Every weight `W` with `vᵀ W v ≥ 0`
gives the same minimizer, which is the paper's remark that `Λ*` does not depend on `W`. `S` is
inverted, so it must be invertible.

The proof completes the square rather than setting a derivative to zero: the Gram matrix of the
generators is `P₊(Λ) = (I - ΛC) R̄ (I - ΛC)ᵀ + Λ Q_v Λᵀ = R̄ + Λ S Λᵀ - Λ Lᵀ - L Λᵀ`, its trace
against `W` is the squared radius ([1, Eq. 11], `fwRadius_sq_eq_trace`), and `trace_gain_le`
minimizes that at `Λ* S = L`, `S` being the Gram matrix of the vectors `C r` (`r` the columns
behind `R̄`) and the columns of `F`.

## References

* [1] Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica, 93:435-443, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n nu nw ny nv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.intersectDescriptor_fwRadius_le (T : Mat ℝ n n) (N : Mat ℝ n ny)
    (A : Mat ℝ n n) (B : Mat ℝ n nu) (D : Mat ℝ n nw) (C : Mat ℝ ny n) (F : Mat ℝ ny nv)
    (u : Vec ℝ nu) (y : Vec ℝ ny) (X : Zonotope (Vec ℝ n)) (W : Mat ℝ n n)
    (hW : ∀ v, 0 ≤ v ⬝ᵥ (W *ᵥ v)) (Λ : Mat ℝ n ny) : -- --- CONCL ---
    let Pbar : Mat ℝ n n := ∑ j, vecMulVec (X.G j) (X.G j)             -- P̄ = H̄ H̄ᵀ
    let Rbar := T * (A * Pbar * Aᵀ + D * Dᵀ) * Tᵀ + N * (F * Fᵀ) * Nᵀ  -- Eq. 15
    let S := C * Rbar * Cᵀ + F * Fᵀ                                    -- Eq. 14
    let L := Rbar * Cᵀ                                                 -- Eq. 13
    IsUnit S.det →
      (X.intersectDescriptor T N (L * S⁻¹) A B D C F u y).fwRadius W ≤
        (X.intersectDescriptor T N Λ A B D C F u y).fwRadius W := by -- --- PROOF ---
  intro Pbar Rbar S L hS
  -- `P̄`, and so `R̄`, is symmetric
  have hPT : Pbarᵀ = Pbar := by simp [Pbar, transpose_sum, transpose_vecMulVec]
  have hRT : Rbarᵀ = Rbar := by
    simp only [Rbar, transpose_add, transpose_mul, transpose_transpose, hPT, Matrix.mul_assoc]
  -- the Gram matrix of the generators, at any `Λ`
  have hG : ∀ Λ' : Mat ℝ n ny,
      ∑ j, vecMulVec ((X.intersectDescriptor T N Λ' A B D C F u y).G j)
        ((X.intersectDescriptor T N Λ' A B D C F u y).G j) =
        Rbar + (Λ' * S * Λ'ᵀ - Λ' * Lᵀ - L * Λ'ᵀ) := by
    intro Λ'
    show ∑ j : Fin (X.h + nw + nv + nv), _ = _
    rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Zonotope.intersectDescriptor, Fin.append_left, Fin.append_right, mulVec_mulVec,
      vecMulVec_mulVec_self, ← Matrix.mul_sum, ← Matrix.sum_mul]
    rw [show ∑ j, vecMulVec (X.G j) (X.G j) = Pbar from rfl]
    simp only [sum_vecMulVec_col]
    -- `(I - Λ'C) R̄ (I - Λ'C)ᵀ + Λ' Q_v Λ'ᵀ`, expanded
    have hL : Lᵀ = C * Rbar := by simp only [L, transpose_mul, transpose_transpose, hRT]
    rw [hL]
    simp only [Rbar, S, L, transpose_mul, transpose_sub, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    abel
  -- `S` is the Gram matrix of the vectors `C r` and the columns of `F`
  let s : ((Fin X.h ⊕ Fin nw) ⊕ Fin nv) ⊕ Fin nv → Vec ℝ ny :=
    Sum.elim (Sum.elim (Sum.elim (fun j => (C * T * A) *ᵥ X.G j) (fun k i => (C * T * D) i k))
      (fun k i => (C * N * F) i k)) (fun k i => F i k)
  have hSs : S = ∑ k, vecMulVec (s k) (s k) := by
    simp only [Fintype.sum_sum_type, s, Sum.elim_inl, Sum.elim_inr, vecMulVec_mulVec_self,
      ← Matrix.mul_sum, ← Matrix.sum_mul]
    rw [show ∑ j, vecMulVec (X.G j) (X.G j) = Pbar from rfl]
    simp only [sum_vecMulVec_col, S, Rbar, transpose_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc]
  have hΛs : L * S⁻¹ * ∑ k, vecMulVec (s k) (s k) = L := by
    rw [← hSs, Matrix.mul_assoc, nonsing_inv_mul _ hS, Matrix.mul_one]
  have key := trace_gain_le W hW s L (L * S⁻¹) Λ hΛs
  rw [← hSs] at key
  -- the squared radii, `tr(W R̄)` plus the bracket `trace_gain_le` compares
  have hsq : ∀ Λ' : Mat ℝ n ny, (X.intersectDescriptor T N Λ' A B D C F u y).fwRadius W ^ 2 =
      trace (W * Rbar) + trace (W * (Λ' * S * Λ'ᵀ - Λ' * Lᵀ - L * Λ'ᵀ)) := fun Λ' => by
    rw [Zonotope.fwRadius_sq_eq_trace W hW, hG, Matrix.mul_add, trace_add]
  have h2 : (X.intersectDescriptor T N (L * S⁻¹) A B D C F u y).fwRadius W ^ 2 ≤
      (X.intersectDescriptor T N Λ A B D C F u y).fwRadius W ^ 2 := by
    rw [hsq, hsq]; linarith
  exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) two_ne_zero).mp h2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
