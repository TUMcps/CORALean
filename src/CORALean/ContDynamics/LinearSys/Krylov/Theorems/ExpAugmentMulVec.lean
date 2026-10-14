module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.AugmentPowMulVec
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegral
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSmulTsum
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpSmul
public import CORALean.ContDynamics.LinearSys.Definitions.MulVecL

@[expose] public section

/-!
# The constant-input solution as an exponential of the augmented matrix

The identity behind the proof of [1, Lemma IV.1]: the first `n`
coordinates of `e^{C̃t}[0ₙ; 1]`, `C̃ = [A u; 0 0]`, are `∫₀ᵗ e^{Aσ}dσ u`. The powers of `C̃` on
the last unit vector are `[A^{k-1}u; 0]` for `k ≥ 1` (`augment_pow_mulVec`), so the exponential
series there is `[Σₖ t^{k+1}/(k+1)! Aᵏ u; 1]`, which is `expIntegral`'s series applied to `u`.

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `P e^{C̃t} [0ₙ; 1] = ∫₀ᵗ e^{Aσ}dσ u`, coordinate by coordinate. -/
theorem Krylov.exp_augment_mulVec_castSucc (A : Mat ℝ n n) (u : Vec ℝ n) (t : ℝ) (j : Fin n) :
    (exp (t • Krylov.augment A u) *ᵥ (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℝ))
        (Fin.castSucc j)
      = (MatExp.expIntegral A t *ᵥ u) j := by -- --- PROOF ---
  set C := Krylov.augment A u with hC
  set e : Fin (n + 1) → ℝ := Pi.single (Fin.last n) 1 with he
  -- both sides as series of vectors, through the continuous map `M ↦ M v`
  have hsL := (mulVecL.flip e).summable (Real.summable_exp_smul C t)
  have hsR := (mulVecL.flip u).summable (MatExp.summable_expIntegral A t)
  have hL : exp (t • C) *ᵥ e
      = ∑' k : ℕ, (((Nat.factorial k : ℝ))⁻¹ * t ^ k) • (C ^ k *ᵥ e) := by
    have h : (∑' k : ℕ, (((Nat.factorial k : ℝ))⁻¹ * t ^ k) • C ^ k) *ᵥ e
        = ∑' k : ℕ, ((((Nat.factorial k : ℝ))⁻¹ * t ^ k) • C ^ k) *ᵥ e :=
      ContinuousLinearMap.map_tsum (mulVecL.flip e) (Real.summable_exp_smul C t)
    rw [Real.exp_smul_tsum, h]
    exact tsum_congr fun k => Matrix.smul_mulVec _ _ _
  have hR : MatExp.expIntegral A t *ᵥ u
      = ∑' k : ℕ, (((Nat.factorial (k + 1) : ℝ))⁻¹ * t ^ (k + 1)) • (A ^ k *ᵥ u) := by
    have h : (∑' k : ℕ, (((Nat.factorial (k + 1) : ℝ))⁻¹ * t ^ (k + 1)) • A ^ k) *ᵥ u
        = ∑' k : ℕ, ((((Nat.factorial (k + 1) : ℝ))⁻¹ * t ^ (k + 1)) • A ^ k) *ᵥ u :=
      ContinuousLinearMap.map_tsum (mulVecL.flip u) (MatExp.summable_expIntegral A t)
    rw [MatExp.expIntegral, h]
    exact tsum_congr fun k => Matrix.smul_mulVec _ _ _
  -- the scalar factor moved out of each term, where `tsum_apply` can read it
  have hsL' : Summable fun k : ℕ => (((Nat.factorial k : ℝ))⁻¹ * t ^ k) • (C ^ k *ᵥ e) :=
    hsL.congr fun k => (Matrix.smul_mulVec _ _ _ : (_ • C ^ k) *ᵥ e = _)
  have hsR' : Summable fun k : ℕ =>
      (((Nat.factorial (k + 1) : ℝ))⁻¹ * t ^ (k + 1)) • (A ^ k *ᵥ u) :=
    hsR.congr fun k => (Matrix.smul_mulVec _ _ _ : (_ • A ^ k) *ᵥ u = _)
  -- read both series at one coordinate; the `k = 0` term of the left one is `e_j = 0`
  rw [hL, hR, tsum_apply hsL', tsum_apply hsR',
    (Pi.summable.1 hsL' (Fin.castSucc j)).tsum_eq_zero_add]
  have h0 : ((((Nat.factorial 0 : ℝ))⁻¹ * t ^ 0) • (C ^ 0 *ᵥ e)) (Fin.castSucc j) = 0 := by
    simp [he, Fin.castSucc_ne_last]
  rw [h0, zero_add]
  refine tsum_congr fun k => ?_
  have hk := congrFun (Krylov.augment_pow_mulVec A u k).1 j
  simp only [Pi.smul_apply, smul_eq_mul] at hk ⊢
  rw [hk]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
