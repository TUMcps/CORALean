import CORALean.HybridDynamics.Operations.TrajectoryError
import CORALean.HybridDynamics.Definitions.SdcInput
import CORALean.HybridDynamics.Operations.SdcFlow
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegralSubSumMemAdaptiveRemainder
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpRemainderMatMono
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSubExpTaylorMemExpRemainderInterval
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpTaylorSmulMulVec
import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact
import CORALean.ContSet.Zonotope.Real.Theorems.MtimesIntervalMatOuter
import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact
import CORALean.ContSet.Zonotope.Real.Theorems.RecentreSubMem
import CORALean.ContSet.Zonotope.Real.Theorems.ScalarIntervalMulOuter
import CORALean.ContSet.Zonotope.Real.Theorems.SumTermsMem

/-!
# `E_err` encloses the error between the linear solution and the constant-derivative one

[1, Eq. 13]: for `t ∈ [tmin, tmax]`, `0 ≤ tmin`, `x₀ ∈ R₀` and `η ≥ 1`, the difference between
the solution `e^{At}x₀ + Γ(t)u` of `ẋ = Ax + u` and the state-dependent constant flow
`y₀ + (Ay₀ + b)t` of [1, Prop. 1], `b = Θ(tc)ξ + Γ*(tc)u`, lies in `E_err`. The Taylor
series are cut at `η` and what they leave, `R(t) x₀` and the tail of `Γ(t) u`, is in `Ê R₀`
and `Ê tmax u`, `Ê(t) ≤ Ê(tmax)` by `expRemainderMat_mono`. Outer only, and at `f₁ = f₂`:
what a nonzero flow correction stands for CORA does not say.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The error, split into the parts `E_err` holds: the exact orders `2…η`, the remainders. -/
theorem aux_trajectoryError_split (A : Mat ℝ n n) (u ξ x₀ : Vec ℝ n) (t tc : ℝ) (η : ℕ) :
    exp (t • A) *ᵥ x₀ + MatExp.expIntegral A t *ᵥ u
        - GuardMap.sdcFlow A (GuardMap.sdcInput A u tc (η + 1) ξ) x₀ t
      = t • (∑ m ∈ Finset.range η, (((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 2)) *ᵥ
          (t ^ (m + 1) • (x₀ - ξ) + (t ^ (m + 1) - tc ^ (m + 1)) • ξ)
        + ∑ m ∈ Finset.range (η + 1), (((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 1)) *ᵥ
          ((t ^ (m + 1) - tc ^ (m + 1)) • u))
      + (exp (t • A) - MatExp.expTaylor (t • A) (η + 1)) *ᵥ x₀
      + (MatExp.expIntegral A t - ∑ i ∈ Finset.range (η + 2), MatExp.particularCoeff A t i) *ᵥ u
      := by -- --- PROOF ---
  -- the exponential's first orders applied to `x₀`: `x₀`, `t A x₀`, then orders `2 … η + 1`
  have hexp : exp (t • A) *ᵥ x₀ = x₀ + t • (A *ᵥ x₀)
      + ∑ m ∈ Finset.range η, (((Nat.factorial (m + 2) : ℝ)⁻¹ * t ^ (m + 2)) • (A ^ (m + 2) *ᵥ x₀))
      + (exp (t • A) - MatExp.expTaylor (t • A) (η + 1)) *ᵥ x₀ := by
    have h := MatExp.expTaylor_smul_mulVec A (η + 1) t x₀
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
    -- the orders `0` and `1` are `x₀` and `t A x₀`
    have h0 : ((Nat.factorial 0 : ℝ)⁻¹ * t ^ 0) • (A ^ 0 *ᵥ x₀) = x₀ := by simp
    have h1 : ((Nat.factorial (0 + 1) : ℝ)⁻¹ * t ^ (0 + 1)) • (A ^ (0 + 1) *ᵥ x₀)
        = t • (A *ᵥ x₀) := by simp
    rw [h0, h1] at h
    -- the shifted indices `k + 1 + 1` and `m + 2` are the same numeral
    have hS : ∑ k ∈ Finset.range η, ((Nat.factorial (k + 1 + 1) : ℝ)⁻¹ * t ^ (k + 1 + 1))
          • (A ^ (k + 1 + 1) *ᵥ x₀)
        = ∑ m ∈ Finset.range η, ((Nat.factorial (m + 2) : ℝ)⁻¹ * t ^ (m + 2))
          • (A ^ (m + 2) *ᵥ x₀) := Finset.sum_congr rfl fun _ _ => rfl
    rw [hS] at h
    have hR : exp (t • A) *ᵥ x₀ = MatExp.expTaylor (t • A) (η + 1) *ᵥ x₀
        + (exp (t • A) - MatExp.expTaylor (t • A) (η + 1)) *ᵥ x₀ := by
      rw [Matrix.sub_mulVec]; abel
    rw [hR, h]
    abel
  -- `Θ(tc) ξ` and `Γ*(tc) u` as sums over the shifted index
  have hΘ : (∑ i ∈ Finset.Ico 2 (η + 1 + 1), (tc ^ (i - 1) / (Nat.factorial i : ℝ)) • A ^ i) *ᵥ ξ
      = ∑ m ∈ Finset.range η,
          ((tc ^ (m + 1) / (Nat.factorial (m + 2) : ℝ)) • (A ^ (m + 2) *ᵥ ξ)) := by
    rw [Matrix.sum_mulVec, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by simp) fun m _ => ?_
    rw [Matrix.smul_mulVec, show 2 + m = m + 2 by ring, show m + 2 - 1 = m + 1 by omega]
  have hΓ : (∑ i ∈ Finset.range (η + 1 + 1), (tc ^ i / ((i + 1).factorial : ℝ)) • A ^ i) *ᵥ u
      = ∑ i ∈ Finset.range (η + 2), ((tc ^ i / ((i + 1).factorial : ℝ)) • (A ^ i *ᵥ u)) := by
    rw [Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun i _ => by rw [Matrix.smul_mulVec]
  -- `Γ(t) u`, its orders and its tail
  have hint : MatExp.expIntegral A t *ᵥ u = ∑ i ∈ Finset.range (η + 2),
      ((t ^ (i + 1) / ((i + 1).factorial : ℝ)) • (A ^ i *ᵥ u))
      + (MatExp.expIntegral A t - ∑ i ∈ Finset.range (η + 2), MatExp.particularCoeff A t i)
        *ᵥ u := by
    rw [Matrix.sub_mulVec, Matrix.sum_mulVec]
    simp only [MatExp.particularCoeff, Matrix.smul_mulVec]
    abel
  -- the state orders against `t Θ(tc) ξ`, termwise
  have EQ1 : ∑ m ∈ Finset.range η, (((Nat.factorial (m + 2) : ℝ)⁻¹ * t ^ (m + 2)) •
        (A ^ (m + 2) *ᵥ x₀)) - t • ∑ m ∈ Finset.range η, ((tc ^ (m + 1)
          / (Nat.factorial (m + 2) : ℝ)) • (A ^ (m + 2) *ᵥ ξ))
      = t • ∑ m ∈ Finset.range η, (((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 2)) *ᵥ
          (t ^ (m + 1) • (x₀ - ξ) + (t ^ (m + 1) - tc ^ (m + 1)) • ξ) := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub]
    module
  -- the input orders against `t Γ*(tc) u`, termwise
  have EQ2 : ∑ m ∈ Finset.range (η + 1), ((t ^ (m + 1 + 1) / (Nat.factorial (m + 1 + 1) : ℝ)) •
        (A ^ (m + 1) *ᵥ u)) - t • ∑ m ∈ Finset.range (η + 1), ((tc ^ (m + 1)
          / (Nat.factorial (m + 1 + 1) : ℝ)) • (A ^ (m + 1) *ᵥ u))
      = t • ∑ m ∈ Finset.range (η + 1), (((Nat.factorial (m + 2) : ℝ)⁻¹) • A ^ (m + 1)) *ᵥ
          ((t ^ (m + 1) - tc ^ (m + 1)) • u) := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Matrix.smul_mulVec, Matrix.mulVec_smul]
    rw [show m + 1 + 1 = m + 2 by rfl]
    module
  simp only [GuardMap.sdcFlow, GuardMap.sdcInput, hΘ, hΓ]
  rw [hexp, hint, Finset.sum_range_succ' (fun i => (t ^ (i + 1) / ((i + 1).factorial : ℝ)) •
    (A ^ i *ᵥ u)), Finset.sum_range_succ' (fun i => (tc ^ i / ((i + 1).factorial : ℝ)) •
    (A ^ i *ᵥ u))]
  simp only [Nat.zero_add, Nat.factorial_one, pow_zero, pow_one, Nat.cast_one,
    div_one, one_smul, Matrix.one_mulVec]
  linear_combination (norm := module) EQ1 + EQ2


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.trajectoryError_outer (sys : LinearSys ℝ n) (f u : Vec ℝ n)
    (R₀ : Zonotope (Vec ℝ n)) {tmin tmax tc : ℝ} (hmin : 0 ≤ tmin) (η : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc tmin tmax) {x₀ : Vec ℝ n} (hx₀ : x₀ ∈ R₀.construct) :
    exp (t • sys.A) *ᵥ x₀ + MatExp.expIntegral sys.A t *ᵥ u
        - GuardMap.sdcFlow sys.A (GuardMap.sdcInput sys.A u tc (η + 1) R₀.c) x₀ t
      ∈ (sys.trajectoryError f f u R₀ tmin tmax tc (η + 1)).construct := by -- --- PROOF ---
  have ht0 : 0 ≤ t := le_trans hmin ht.1
  -- `E_err` as its four summands, the vector as its four parts
  simp only [LinearSys.trajectoryError, Nat.add_sub_cancel]
  rw [aux_trajectoryError_split, ← Zonotope.plus_exact, ← Zonotope.plus_exact,
    ← Zonotope.plus_exact]
  have hvec : ∀ a b c : Vec ℝ n, a + b + c = a + b + c + t • (f - f) := by
    intro a b c; rw [sub_self, smul_zero, add_zero]
  rw [hvec]
  -- the intervals the powers of `t` and their shifts by `tc` sit in
  have hpow : ∀ k : ℕ, t ^ k ∈ Set.Icc (tmin ^ k) (tmax ^ k) := fun k =>
    ⟨pow_le_pow_left₀ hmin ht.1 k, pow_le_pow_left₀ ht0 ht.2 k⟩
  have hpow' : ∀ k : ℕ, t ^ k - tc ^ k ∈ Set.Icc (tmin ^ k - tc ^ k) (tmax ^ k - tc ^ k) :=
    fun k => ⟨sub_le_sub_right (hpow k).1 _, sub_le_sub_right (hpow k).2 _⟩
  have hY : x₀ - R₀.c ∈ R₀.recentre.construct := Zonotope.sub_centre_mem_recentre hx₀
  refine Set.add_mem_add (Set.add_mem_add (Set.add_mem_add ?_ ?_) ?_) ?_
  · -- the exact orders: `t` times the two sums, each a sum of members of its terms
    refine Zonotope.scalarIntervalMul_outer _ _ _ ht ?_
    rw [← Zonotope.plus_exact]
    refine Set.add_mem_add (Zonotope.sum_mem_sumTerms _ _ _ fun m _ => ?_)
      (Zonotope.sum_mem_sumTerms _ _ _ fun m _ => ?_)
    · rw [← Zonotope.mtimes_exact, ← Zonotope.plus_exact]
      exact ⟨_, Set.add_mem_add (Zonotope.scalarIntervalMul_outer _ _ _ (hpow (m + 1)) hY)
        (Zonotope.scalarIntervalMul_outer _ _ _ (hpow' (m + 1)) (Zonotope.mem_ofPoint _)), rfl⟩
    · rw [← Zonotope.mtimes_exact]
      exact ⟨_, Zonotope.scalarIntervalMul_outer _ _ _ (hpow' (m + 1)) (Zonotope.mem_ofPoint _),
        rfl⟩
  · -- the exponential's remainder `R(t)` is within `Ê(tmax)`, entrywise
    have hR := MatExp.exp_sub_expTaylor_mem_expRemainderInterval sys.A ht0 (η + 1)
    refine Zonotope.mtimesIntervalMat_outer _ _ (Set.mem_biUnion ?_ (Set.mem_image_of_mem _ hx₀))
    refine Interval.mem_mat_iff.mpr fun j k => ?_
    have h12 := le_trans (hR j k) (MatExp.expRemainderMat_mono sys.A ht0 ht.2 (η + 1) j k)
    have h3 := le_abs_self (MatExp.expRemainderMat sys.A tmax (η + 1) j k)
    exact abs_le.mp (le_trans h12 h3)
  · -- the tail of `Γ(t)`, `t Ê(t) ≤ tmax |Ê(tmax)|`
    have hb := MatExp.abs_particularTail_entry_le sys.A ht0 (η + 1)
    refine Zonotope.mtimesIntervalMat_outer _ _ (Set.mem_biUnion ?_
      (Set.mem_image_of_mem _ (Zonotope.mem_ofPoint u)))
    refine Interval.mem_mat_iff.mpr fun j k => ?_
    have h1 := MatExp.expRemainderMat_mono sys.A ht0 ht.2 (η + 1) j k
    have h2 := le_abs_self (MatExp.expRemainderMat sys.A tmax (η + 1) j k)
    have h3 := abs_nonneg (MatExp.expRemainderMat sys.A tmax (η + 1) j k)
    have h4 : t * MatExp.expRemainderMat sys.A t (η + 1) j k
        ≤ tmax * |MatExp.expRemainderMat sys.A tmax (η + 1) j k| := by
      calc t * MatExp.expRemainderMat sys.A t (η + 1) j k
          ≤ t * |MatExp.expRemainderMat sys.A tmax (η + 1) j k| :=
            mul_le_mul_of_nonneg_left (le_trans h1 h2) ht0
        _ ≤ tmax * |MatExp.expRemainderMat sys.A tmax (η + 1) j k| :=
            mul_le_mul_of_nonneg_right ht.2 h3
    have h5 := abs_le.mp (hb j k)
    simp only [MatExp.adaptiveRemainder]
    exact ⟨by linarith [h5.1], by linarith [h5.2]⟩
  · -- the flow correction, `t (f - f) = 0`
    exact Zonotope.scalarIntervalMul_outer _ _ _ ht (Zonotope.mem_ofPoint _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
