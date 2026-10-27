module

public import CORALean.ContSet.Zonotope.Real.Operations.ObserveDescriptor
public import CORALean.ContSet.Zonotope.Real.Theorems.FWRadiusSqEqTrace
public import CORALean.Global.TraceGainLe
public import CORALean.Global.SumVecMulVecCol
public import CORALean.Global.VecMulVecMulVecSelf
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The optimal Kalman observer gain

[1, Thm. 6]: among all gains `G`, the state-bounding zonotope `⟨p̂₊(G), Ĥ₊(G)⟩` of Eq. 31 of
[1, Thm. 5] has the least F_W-radius at `G* = TA K` (Eq. 32), `K = L̃ S̃⁻¹`, `L̃ = P̃ Cᵀ`,
`S̃ = C P̃ Cᵀ + Q_v` (Eq. 33-35), `P̃ = H̄ H̄ᵀ`, `Q_v = F Fᵀ`, for every weight `W` with
`vᵀ W v ≥ 0`. `S̃` is inverted, so it must be invertible. The Gram matrix of the generators is
`(TA - GC) P̃ (TA - GC)ᵀ + T Q_w Tᵀ + N Q_v Nᵀ + G Q_v Gᵀ`, the part free of `G` plus
`G S̃ Gᵀ - G (TA L̃)ᵀ - (TA L̃) Gᵀ`, so `trace_gain_le` minimizes its trace against `W` at any `G`
with `G S̃ = TA L̃`, which `TA L̃ S̃⁻¹` is.

## Inputs
* `T` – decoupling matrix
* `N` – measurement decoupling matrix
* `A` – state matrix
* `B` – input matrix
* `D` – disturbance matrix
* `C` – output matrix
* `F` – noise matrix
* `u` – control input
* `y` – current output
* `y_plus` – next output
* `X` – state zonotope
* `W` – weight matrix
* `G` – competing gain

## Hypotheses
* `hW` – `W` positive semidefinite

## Conclusion
* the optimal gain minimizes the weighted Frobenius radius

## References

* [1] [Y. Wang, V. Puig and G. Cembrano. "Set-membership approach and Kalman observer based on
      zonotopes for discrete-time descriptor systems". Automatica,
      2018.](../../../../../../references/2018/wang-automatica-descriptor-observer.md)
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

theorem Zonotope.observeDescriptor_fwRadius_le (T : Mat ℝ n n) (N : Mat ℝ n ny)
    (A : Mat ℝ n n) (B : Mat ℝ n nu) (D : Mat ℝ n nw) (C : Mat ℝ ny n) (F : Mat ℝ ny nv)
    (u : Vec ℝ nu) (y y_plus : Vec ℝ ny) (X : Zonotope (Vec ℝ n)) (W : Mat ℝ n n)
    (hW : ∀ v, 0 ≤ v ⬝ᵥ (W *ᵥ v)) (G : Mat ℝ n ny) : -- --- CONCL ---
    let Ptilde : Mat ℝ n n := ∑ j, vecMulVec (X.G j) (X.G j)          -- P̃ = H̄ H̄ᵀ
    let Ltilde := Ptilde * Cᵀ                                          -- Eq. 34
    let Stilde := C * Ptilde * Cᵀ + F * Fᵀ                             -- Eq. 35
    let K := Ltilde * Stilde⁻¹                                         -- Eq. 33
    IsUnit Stilde.det →
      (X.observeDescriptor T N (T * A * K) A B D C F u y y_plus).fwRadius W ≤
        (X.observeDescriptor T N G A B D C F u y y_plus).fwRadius W := by -- --- PROOF ---
  intro Ptilde Ltilde Stilde K hS
  have hPT : Ptildeᵀ = Ptilde := by simp [Ptilde, transpose_sum, transpose_vecMulVec]
  set L := T * A * Ltilde
  -- the Gram matrix of the generators, at any gain
  have hG : ∀ G' : Mat ℝ n ny,
      ∑ j, vecMulVec ((X.observeDescriptor T N G' A B D C F u y y_plus).G j)
        ((X.observeDescriptor T N G' A B D C F u y y_plus).G j) =
        (T * A * Ptilde * Aᵀ * Tᵀ + T * D * Dᵀ * Tᵀ + N * F * Fᵀ * Nᵀ) +
          (G' * Stilde * G'ᵀ - G' * Lᵀ - L * G'ᵀ) := by
    intro G'
    show ∑ j : Fin (X.h + nw + nv + nv), _ = _
    rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Zonotope.observeDescriptor, Fin.append_left, Fin.append_right,
      vecMulVec_mulVec_self, ← Matrix.mul_sum, ← Matrix.sum_mul]
    rw [show ∑ j, vecMulVec (X.G j) (X.G j) = Ptilde from rfl]
    have hneg : ∀ {k : ℕ} (M : Mat ℝ n k),
        ∑ j, vecMulVec (fun i => -M i j) (fun i => -M i j) = M * Mᵀ := fun M => by
      rw [← sum_vecMulVec_col]; simp [vecMulVec]
    rw [hneg, hneg, sum_vecMulVec_col]
    -- `(TA - G'C) P̃ (TA - G'C)ᵀ`, expanded
    simp only [L, Ltilde, Stilde, transpose_mul, transpose_sub, transpose_transpose, hPT,
      Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  -- `S̃` is the Gram matrix of the `C h̄ⱼ` and the columns of `F`
  let s : Fin X.h ⊕ Fin nv → Vec ℝ ny :=
    Sum.elim (fun j => C *ᵥ X.G j) (fun k i => F i k)
  have hSs : Stilde = ∑ k, vecMulVec (s k) (s k) := by
    simp only [Fintype.sum_sum_type, s, Sum.elim_inl, Sum.elim_inr, vecMulVec_mulVec_self,
      ← Matrix.mul_sum, ← Matrix.sum_mul]
    rw [show ∑ j, vecMulVec (X.G j) (X.G j) = Ptilde from rfl, sum_vecMulVec_col]
  have hΛs : T * A * K * ∑ k, vecMulVec (s k) (s k) = L := by
    rw [← hSs, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hS,
      Matrix.mul_one, ← Matrix.mul_assoc]
  have key := trace_gain_le W hW s L (T * A * K) G hΛs
  rw [← hSs] at key
  -- the squared radii, a part free of the gain plus the bracket `trace_gain_le` compares
  have hsq : ∀ G' : Mat ℝ n ny,
      (X.observeDescriptor T N G' A B D C F u y y_plus).fwRadius W ^ 2 =
        trace (W * (T * A * Ptilde * Aᵀ * Tᵀ + T * D * Dᵀ * Tᵀ + N * F * Fᵀ * Nᵀ)) +
          trace (W * (G' * Stilde * G'ᵀ - G' * Lᵀ - L * G'ᵀ)) := fun G' => by
    rw [Zonotope.fwRadius_sq_eq_trace W hW, hG, Matrix.mul_add, trace_add]
  have h2 : (X.observeDescriptor T N (T * A * K) A B D C F u y y_plus).fwRadius W ^ 2 ≤
      (X.observeDescriptor T N G A B D C F u y y_plus).fwRadius W ^ 2 := by
    rw [hsq, hsq]; linarith
  exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) two_ne_zero).mp h2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
