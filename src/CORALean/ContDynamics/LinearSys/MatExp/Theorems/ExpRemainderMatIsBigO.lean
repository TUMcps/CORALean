module

public import CORALean.ContDynamics.LinearSys.MatExp.Definitions.ExpRemainderMat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe

@[expose] public section

/-!
# `Lemma 1`, the rate half: the entrywise remainder is `O(Δtᵂ⁺¹)`

[1, Lemma 1]: `E(Δt,η) ∼ O(Δtᵂ⁺¹)` as `Δt → 0⁺`. Once `Δt · ‖absMat A‖ ≤ (η+2)/2`
— eventually true, as in `tendsto_expRemainderMat_zero` — the geometric factor
of `expRemainderBound` is capped at `2` instead of merely bounded, which turns
`norm_exp_sub_expTaylor_le`'s bound into an explicit constant times `Δtᵂ⁺¹`: the
leading term of the remainder's own Taylor series, `A`'s norm folded into the
constant.

## Inputs
* `A` – system matrix
* `η` – Taylor order

## Hypotheses
* none

## Conclusion
* the entrywise remainder is of order one power higher than the Taylor order in the step

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Inner- and Outer-Approximations of
      Reachable Sets". IEEE Transactions on Automatic Control, vol. 68, no. 12,
      2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Filter Topology Asymptotics

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1], the rate half: the entrywise exponential remainder is
`O(Δtᵂ⁺¹)` as the step shrinks to `0`, at any fixed order. -/
theorem MatExp.expRemainderMat_isBigO (A : Mat ℝ n n) (η : ℕ) : -- --- CONCL ---
    (fun Δt : ℝ => MatExp.expRemainderMat A Δt η)
      =O[𝓝[>] (0 : ℝ)] fun Δt : ℝ => Δt ^ (η + 1) := by -- --- PROOF ---
  refine IsBigO.of_bound (2 * ‖MatExp.absMat A‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) ?_
  have hid : Tendsto (fun Δt : ℝ => Δt) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hnorm : Tendsto (fun Δt : ℝ => Δt * ‖MatExp.absMat A‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hid.mul_const ‖MatExp.absMat A‖
  have hle : ∀ᶠ Δt : ℝ in 𝓝[>] (0 : ℝ), Δt * ‖MatExp.absMat A‖ ≤ ((η : ℝ) + 2) / 2 :=
    hnorm.eventually_le_const (by positivity)
  filter_upwards [hle, self_mem_nhdsWithin] with Δt hΔt hΔtpos
  set c := ‖MatExp.absMat A‖
  -- `Δt · c ≤ (η+2)/2` puts the geometric factor at ≤ 2 instead of merely bounded
  have hxnorm : ‖Δt • MatExp.absMat A‖ = Δt * c := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hΔtpos]
  have hfrac_le : ‖Δt • MatExp.absMat A‖ / ((η : ℝ) + 2) ≤ 1 / 2 := by
    rw [hxnorm, div_le_iff₀ (by positivity : (0:ℝ) < (η:ℝ) + 2)]
    linarith
  have hεx : ‖Δt • MatExp.absMat A‖ / ((η : ℝ) + 2) < 1 := lt_of_le_of_lt hfrac_le (by norm_num)
  have hgeom_pos : (0 : ℝ) < 1 - ‖Δt • MatExp.absMat A‖ / ((η : ℝ) + 2) := by linarith
  have hgeom_le : (1 - ‖Δt • MatExp.absMat A‖ / ((η : ℝ) + 2))⁻¹ ≤ 2 := by
    have h := inv_anti₀ (by norm_num : (0:ℝ) < 1 / 2) (by linarith : (1:ℝ) / 2 ≤
      1 - ‖Δt • MatExp.absMat A‖ / ((η : ℝ) + 2))
    simpa using h
  have hbound : ‖MatExp.expRemainderMat A Δt η‖ ≤ MatExp.expRemainderBound
      (Δt • MatExp.absMat A) η :=
    norm_exp_sub_expTaylor_le _ η hεx
  have hnum_nonneg : (0 : ℝ) ≤ ‖Δt • MatExp.absMat A‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) := by
    positivity
  have hpow : ‖Δt • MatExp.absMat A‖ ^ (η + 1) = Δt ^ (η + 1) * c ^ (η + 1) := by
    rw [hxnorm, mul_pow]
  -- fold the capped geometric factor in, then read the leading term back out as `Δtᵂ⁺¹`
  calc ‖MatExp.expRemainderMat A Δt η‖
      ≤ MatExp.expRemainderBound (Δt • MatExp.absMat A) η := hbound
    _ = (‖Δt • MatExp.absMat A‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ))
        * (1 - ‖Δt • MatExp.absMat A‖ / ((η : ℝ) + 2))⁻¹ := rfl
    _ ≤ (‖Δt • MatExp.absMat A‖ ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) * 2 :=
        mul_le_mul_of_nonneg_left hgeom_le hnum_nonneg
    _ = (Δt ^ (η + 1) * c ^ (η + 1) / (Nat.factorial (η + 1) : ℝ)) * 2 := by rw [hpow]
    _ = 2 * c ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) * Δt ^ (η + 1) := by ring
    _ = 2 * c ^ (η + 1) / (Nat.factorial (η + 1) : ℝ) * ‖Δt ^ (η + 1)‖ := by
        rw [Real.norm_eq_abs, abs_of_pos (pow_pos hΔtpos _)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
