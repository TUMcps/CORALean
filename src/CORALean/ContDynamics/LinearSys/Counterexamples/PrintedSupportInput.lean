module

public import CORALean.ContDynamics.LinearSys.Definitions.HeldSim
public import CORALean.Global.Float.Instances.Real.Theorems.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import CORALean.ContDynamics.LinearSys.Operations.Canonical

@[expose] public section

/-!
# [1]'s Eq. (20) as printed does not reach the support vector

[1, Sec. 4.2] simulates [1]'s Eq. (18) from `x(0) = ν(X₀, (e^{A t_k})ᵀ ℓ)` under
`u(j) = ν(U₀, (e^{A t_j})ᵀ ℓ) + ũ` [1]'s Eq. (20) and calls `x(k)` the support vector of the
set reached under piecewise-constant inputs. (18) multiplies `u(j)` by `T = ∫₀^{Δt} e^{Aσ} dσ`
before `e^{A t_{k-1-j}}`, so the maximizing direction is `(e^{A t_{k-1-j}} T)ᵀ ℓ`; the printed
one drops `T` and counts from the wrong end. For `A = [[0, 1], [0, 0]]`, `Δt = 1`, `X₀ = {0}`,
`U = [-1, 1]²`, `ℓ = (1, -1/4)` the printed input `(1, -1)` reaches `3/4`, the input `(1, 1)`
reaches `5/4`. `supportCounterexample` uses the corrected direction.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the printed inputs do not always reach furthest along the direction

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control,
      2023.](../../../../../references/2023/wetzlinger-hscc-support-functions.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `T = I + A/2` for the nilpotent `A = [[0, 1], [0, 0]]` and `Δt = 1`: the series stops. -/
private theorem aux_expIntegral_nilpotent : -- --- CONCL ---
    MatExp.expIntegral (!![0, 1; 0, 0] : Mat ℝ 2 2) 1
      = 1 + (1 / 2 : ℝ) • !![0, 1; 0, 0] := by -- --- PROOF ---
  have hA2 : (!![0, 1; 0, 0] : Mat ℝ 2 2) ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  have hpow : ∀ i ≥ 2, (!![0, 1; 0, 0] : Mat ℝ 2 2) ^ i = 0 := fun i hi => by
    rw [← Nat.add_sub_cancel' hi, pow_add, hA2, zero_mul]
  rw [MatExp.expIntegral, tsum_eq_sum (s := Finset.range 2) fun i hi => by
    rw [hpow i (by simp at hi; omega), smul_zero]]
  simp [Finset.sum_range_succ]

/-- The box `[-1, 1]²`'s support vector: each coordinate's sign along `d`. -/
private theorem aux_box_support (d : Vec ℝ 2 →ₗ[ℝ] ℝ) (y : Vec ℝ 2)
    (hy : ∀ i, |y i| ≤ 1) : -- --- CONCL ---
    d y ≤ d ![if 0 ≤ d (Pi.single 0 1) then 1 else -1,
      if 0 ≤ d (Pi.single 1 1) then 1 else -1] := by -- --- PROOF ---
  have hsplit : ∀ z : Vec ℝ 2, d z = z 0 * d (Pi.single 0 1) + z 1 * d (Pi.single 1 1) := by
    intro z
    have hz : z = z 0 • (Pi.single 0 1 : Vec ℝ 2) + z 1 • (Pi.single 1 1 : Vec ℝ 2) := by
      ext i; fin_cases i <;> simp
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hterm : ∀ (a c : ℝ), |a| ≤ 1 → a * c ≤ (if 0 ≤ c then 1 else -1) * c := by
    intro a c ha
    have h1 := le_abs_self (a * c)
    rw [abs_mul] at h1
    have h3 : a * c ≤ |c| := h1.trans (mul_le_of_le_one_left (abs_nonneg c) ha)
    split_ifs with hc
    · rw [abs_of_nonneg hc] at h3; linarith
    · rw [abs_of_neg (not_le.mp hc)] at h3; linarith
  calc d y = y 0 * d (Pi.single 0 1) + y 1 * d (Pi.single 1 1) := hsplit y
    _ ≤ (if 0 ≤ d (Pi.single 0 1) then 1 else -1) * d (Pi.single 0 1)
        + (if 0 ≤ d (Pi.single 1 1) then 1 else -1) * d (Pi.single 1 1) :=
      add_le_add (hterm _ _ (hy 0)) (hterm _ _ (hy 1))
    _ = _ := by rw [hsplit ![_, _]]; simp


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2] as printed: from `x(0) = 0` under `u(j) = ν(U, (e^{A t_j})ᵀ ℓ)` (that is,
(20) with `ũ = 0`), [1]'s Eq. (18) reaches at least as far along `ℓ` as under any other inputs
in `U`. -/
theorem LinearSys.printedSupportInput_counterexample : -- --- CONCL ---
    ¬ ∀ (n : ℕ) (sys : LinearSys ℝ n) (Δt : ℝ), 0 < Δt →
      ∀ (U : Set (Vec ℝ n)) (νU : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n),
        (∀ d, νU d ∈ U ∧ ∀ y ∈ U, d y ≤ d (νU d)) →
        ∀ (ℓ : Vec ℝ n →ₗ[ℝ] ℝ) (k : ℕ) (u' : ℕ → Vec ℝ n), (∀ j, u' j ∈ U) →
          ℓ (sys.heldSim Δt 0 u' k)
            ≤ ℓ (sys.heldSim Δt 0 (fun j => νU (ℓ.comp
                (mulVecLin (exp (((j : ℝ) * Δt) • toRealMat sys.A)))))
                k) := by -- --- PROOF ---
  intro h
  let U : Set (Vec ℝ 2) := {y | ∀ i, |y i| ≤ 1}
  let νU : (Vec ℝ 2 →ₗ[ℝ] ℝ) → Vec ℝ 2 := fun d =>
    ![if 0 ≤ d (Pi.single 0 1) then 1 else -1, if 0 ≤ d (Pi.single 1 1) then 1 else -1]
  have hνU : ∀ d, νU d ∈ U ∧ ∀ y ∈ U, d y ≤ d (νU d) := fun d => by
    refine ⟨fun i => ?_, fun y hy => aux_box_support d y hy⟩
    fin_cases i <;> simp only [νU] <;> split_ifs <;> norm_num
  let ℓ : Vec ℝ 2 →ₗ[ℝ] ℝ := LinearMap.proj 0 - (1 / 4 : ℝ) • LinearMap.proj 1
  have hu' : ∀ _ : ℕ, (![1, 1] : Vec ℝ 2) ∈ U := fun _ i => by fin_cases i <;> simp
  have key := h 2 (LinearSys.canonical !![0, 1; 0, 0]) 1 one_pos U νU hνU ℓ 1 (fun _ => ![1, 1]) hu'
  -- the printed input at `j = 0` is `ν(U, ℓ) = (1, -1)`
  have hν : νU (ℓ.comp (mulVecLin (exp ((((0 : ℕ) : ℝ) * 1) • toRealMat
      (LinearSys.canonical !![0, 1; 0, 0] : LinearSys ℝ 2).A)))) = ![1, -1] := by
    simp only [Nat.cast_zero, zero_mul, zero_smul, exp_zero, Matrix.mulVecLin_one,
      LinearMap.comp_id, νU, ℓ]
    ext i; fin_cases i <;> norm_num
  have hstep : ∀ u : ℕ → Vec ℝ 2, (LinearSys.canonical !![0, 1; 0, 0] : LinearSys ℝ 2).heldSim 1 0
      u 1
      = (1 + (1 / 2 : ℝ) • !![0, 1; 0, 0] : Mat ℝ 2 2) *ᵥ u 0 := fun u => by
    show _ *ᵥ (0 : Vec ℝ 2) + _ = _
    rw [mulVec_zero, zero_add, toRealMat_real, aux_expIntegral_nilpotent]
  rw [hstep, hstep, hν] at key
  simp [ℓ, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at key
  norm_num at key

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
