module

public import CORALean.ContDynamics.LinearSys.Theorems.HeldSimEq
public import CORALean.ContDynamics.LinearSys.Operations.SupportCounterexample
public import CORALean.ContDynamics.LinearSys.Operations.SupportLower
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-!
# The corrected counterexample reaches the lower bound exactly

[1, Sec. 4.2]: simulating [1]'s Eq. (18) from the initial state of [1]'s Eq. (19) under the inputs
of [1]'s Eq. (20) lands, at `t_k`, on a point whose value along `ℓ` *is* line 15's `ρ(Ř(t_k), ℓ)` of
[1, Alg. 1 (lower bounds)]: an equality, not a bound, with the inputs of `supportCounterexample`,
which runs the steps from the end and applies `T`. Both sides are read in closed form: `heldSim` as
`e^{AΔt k} x₀` plus each input carried forward by `e^{AΔt (k-1-i)} T`, and `supportLower`'s fields
as sums over the steps. Line 15 then sums `ρ(X₀, d_k)`, the constant input's `ℓ(P_u(t_k))` and line
14's `ρ(T U₀, d_j) = ρ(T U, d_j) - d_j(T ũ)`, where the two `ũ` terms cancel, so the value does not
depend on which point of `U` line 2 calls its center.

## Inputs
* `sys` – linear system
* `Δt` – step length
* `ν₀` – support vector map of the initial set
* `νU` – support vector map of the input set
* `c` – point of the input set
* `ℓ` – direction
* `k` – step index

## Hypotheses
* none

## Conclusion
* the counterexample's state attains the lower bound along the direction

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Reachability Analysis with Support Functions". Proceedings of the 26th ACM
      International Conference on Hybrid Systems: Computation and Control, 2023.
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

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Line 8 in closed form: `d_k = ℓ ∘ e^{AΔt k}`. -/
theorem aux_supportLower_d (sys : LinearSys 𝕋 n) (Δt : ℝ)
    (ν₀ νU : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n) (c : Vec ℝ n) (ℓ : Vec ℝ n →ₗ[ℝ] ℝ)
    (k : ℕ) : -- --- CONCL ---
    (sys.supportLower Δt ν₀ νU c ℓ k).d
      = ℓ.comp (mulVecLin (exp (Δt • toRealMat sys.A) ^ k)) := by -- --- PROOF ---
  induction k with
  | zero =>
    show ℓ = _
    rw [pow_zero, Matrix.mulVecLin_one, LinearMap.comp_id]
  | succ k ih =>
    show (sys.supportLower Δt ν₀ νU c ℓ k).d.comp (mulVecLin (exp (Δt • toRealMat sys.A))) = _
    rw [ih, pow_succ, Matrix.mulVecLin_mul, LinearMap.comp_assoc]

/-- Line 9 in closed form: `P_u(t_k) = ∑_{j<k} e^{AΔt j} T ũ`. -/
theorem aux_supportLower_Pu (sys : LinearSys 𝕋 n) (Δt : ℝ)
    (ν₀ νU : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n) (c : Vec ℝ n) (ℓ : Vec ℝ n →ₗ[ℝ] ℝ)
    (k : ℕ) : -- --- CONCL ---
    (sys.supportLower Δt ν₀ νU c ℓ k).Pu
      = ∑ j ∈ Finset.range k, exp (Δt • toRealMat sys.A) ^ j *ᵥ
          (MatExp.expIntegral (toRealMat sys.A) Δt *ᵥ c) := by -- --- PROOF ---
  induction k with
  | zero => rfl
  | succ k ih =>
    show exp (Δt • toRealMat sys.A) *ᵥ (sys.supportLower Δt ν₀ νU c ℓ k).Pu
      + MatExp.expIntegral (toRealMat sys.A) Δt *ᵥ c = _
    rw [ih, Finset.sum_range_succ', pow_zero, one_mulVec, Matrix.mulVec_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mulVec_mulVec, pow_succ']

/-- The direction `ℓ` pulled back through `j` steps and the input integral, `d_j` of line 14. -/
noncomputable def aux_supportDir (sys : LinearSys 𝕋 n) (Δt : ℝ) (ℓ : Vec ℝ n →ₗ[ℝ] ℝ) (j : ℕ) :
    Vec ℝ n →ₗ[ℝ] ℝ :=
  (ℓ.comp (mulVecLin (exp (Δt • toRealMat sys.A) ^ j))).comp
    (mulVecLin (MatExp.expIntegral (toRealMat sys.A) Δt))

/-- Line 14 in closed form: `ρ(P̌_U(t_k), ℓ) = ∑_{j<k} ρ(T U₀, d_j)`. -/
theorem aux_supportLower_ρP (sys : LinearSys 𝕋 n) (Δt : ℝ)
    (ν₀ νU : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n) (c : Vec ℝ n) (ℓ : Vec ℝ n →ₗ[ℝ] ℝ)
    (k : ℕ) : -- --- CONCL ---
    (sys.supportLower Δt ν₀ νU c ℓ k).ρP
      = ∑ j ∈ Finset.range k,
          (aux_supportDir sys Δt ℓ j (νU (aux_supportDir sys Δt ℓ j))
            - aux_supportDir sys Δt ℓ j c) := by -- --- PROOF ---
  induction k with
  | zero => rfl
  | succ k ih =>
    -- the direction pulled back through the stored `d`
    set D := ((sys.supportLower Δt ν₀ νU c ℓ k).d).comp
      (mulVecLin (MatExp.expIntegral (toRealMat sys.A) Δt)) with hD
    show (sys.supportLower Δt ν₀ νU c ℓ k).ρP
      + (D
          (νU D)
        - D c) = _
    rw [ih, Finset.sum_range_succ]
    simp only [hD, aux_supportLower_d]
    rfl

/-- Lines 10 and 15 at any step, the first step included. -/
theorem aux_supportLower_ρR (sys : LinearSys 𝕋 n) (Δt : ℝ)
    (ν₀ νU : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n) (c : Vec ℝ n) (ℓ : Vec ℝ n →ₗ[ℝ] ℝ)
    (k : ℕ) : -- --- CONCL ---
    (sys.supportLower Δt ν₀ νU c ℓ k).ρR
      = (sys.supportLower Δt ν₀ νU c ℓ k).d (ν₀ (sys.supportLower Δt ν₀ νU c ℓ k).d)
        + ℓ (sys.supportLower Δt ν₀ νU c ℓ k).Pu
        + (sys.supportLower Δt ν₀ νU c ℓ k).ρP := by -- --- PROOF ---
  cases k with
  | zero =>
    show ℓ (ν₀ ℓ) + 0 = ℓ (ν₀ ℓ) + ℓ 0 + 0
    simp
  | succ k => rfl


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2], with [1]'s Eq. (20) corrected: the state [1]'s Eq. (18) reaches at `t_k` from
`supportCounterexample` has, along `ℓ`, exactly line 15's lower bound `ρ(Ř(t_k), ℓ)`. -/
theorem LinearSys.heldSim_supportCounterexample (sys : LinearSys 𝕋 n) (Δt : ℝ)
    (ν₀ νU : (Vec ℝ n →ₗ[ℝ] ℝ) → Vec ℝ n) (c : Vec ℝ n) (ℓ : Vec ℝ n →ₗ[ℝ] ℝ)
    (k : ℕ) : -- --- CONCL ---
    ℓ (sys.heldSim Δt (sys.supportCounterexample Δt ν₀ νU ℓ k).1
        (sys.supportCounterexample Δt ν₀ νU ℓ k).2 k)
      = (sys.supportLower Δt ν₀ νU c ℓ k).ρR := by -- --- PROOF ---
  set Φ := exp (Δt • toRealMat sys.A)
  set T := MatExp.expIntegral (toRealMat sys.A) Δt
  -- `g j = ρ(T U, d_j)`, the value line 14 adds at step `j` before `ũ` is taken off
  set g : ℕ → ℝ := fun j => ((ℓ.comp (mulVecLin (Φ ^ j))).comp (mulVecLin T))
    (νU ((ℓ.comp (mulVecLin (Φ ^ j))).comp (mulVecLin T)))
  rw [aux_supportLower_ρR, aux_supportLower_ρP, aux_supportLower_Pu, aux_supportLower_d,
    LinearSys.heldSim_eq, map_add, map_sum, map_sum, Finset.sum_sub_distrib]
  unfold aux_supportDir
  -- the constant input's `ℓ(P_u(t_k))` is the `ũ` line 14 takes off, so the two cancel
  have hũ : ∑ j ∈ Finset.range k, ℓ (Φ ^ j *ᵥ (T *ᵥ c))
      = ∑ j ∈ Finset.range k, ((ℓ.comp (mulVecLin (Φ ^ j))).comp (mulVecLin T)) c := rfl
  rw [hũ, add_assoc, add_sub_cancel]
  congr 1
  rw [← Finset.sum_range_reflect g k]
  refine Finset.sum_congr rfl fun i _ => ?_
  rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
