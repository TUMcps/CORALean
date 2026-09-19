import CORALean.ContDynamics.LinearSys.MatExp.ExpRemainderMat
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSubExpTaylorLe
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoExpRemainderBoundZero

/-!
# `Lemma 1`, the limit half: the entrywise remainder vanishes with the step

[1, Lemma 1]: `E(Δt,η) → 0` as `Δt → 0⁺`. `expRemainderMat A Δt η` is, by
definition, `exp x − expTaylor x η` at `x = Δt • absMat A`, so its norm is
squeezed between `0` and `expRemainderBound x η`, once `Δt` is small enough for
`norm_exp_sub_expTaylor_le`'s side condition to hold — which it eventually
does, since `‖x‖ = Δt · ‖absMat A‖ → 0`. `tendsto_expRemainderBound_zero`
carries that bound itself to `0`, and `tendsto_zero_iff_norm_tendsto_zero`
turns the squeezed norm back into convergence of the matrix.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Inner- and Outer-Approximations of
      Reachable Sets". IEEE Transactions on Automatic Control, vol. 68, no. 12,
      2023, pp. 7771–7786.
-/

-- Authors:       Tobias Ladner
-- Written:       19-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1], the limit half: the entrywise exponential remainder vanishes
as the step shrinks to `0`, at any fixed order. -/
theorem MatExp.tendsto_expRemainderMat_zero (A : Mat ℝ n n) (η : ℕ) :
    Tendsto (fun Δt : ℝ => MatExp.expRemainderMat A Δt η)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by -- --- PROOF ---
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (MatExp.tendsto_expRemainderBound_zero (MatExp.absMat A) η)
  -- once `Δt · ‖absMat A‖ < η + 2`, `norm_exp_sub_expTaylor_le`'s side condition holds
  have hid : Tendsto (fun Δt : ℝ => Δt) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hnorm : Tendsto (fun Δt : ℝ => Δt * ‖MatExp.absMat A‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hid.mul_const ‖MatExp.absMat A‖
  have hlt : ∀ᶠ Δt : ℝ in 𝓝[>] (0 : ℝ), Δt * ‖MatExp.absMat A‖ < (η : ℝ) + 2 :=
    hnorm.eventually_lt tendsto_const_nhds (by positivity)
  filter_upwards [hlt, self_mem_nhdsWithin] with Δt hΔt hΔtpos
  have hεx : ‖Δt • MatExp.absMat A‖ / ((η : ℝ) + 2) < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hΔtpos, div_lt_one (by positivity)]
    exact hΔt
  calc ‖MatExp.expRemainderMat A Δt η‖
      = ‖exp (Δt • MatExp.absMat A) - MatExp.expTaylor (Δt • MatExp.absMat A) η‖ := rfl
    _ ≤ MatExp.expRemainderBound (Δt • MatExp.absMat A) η :=
        norm_exp_sub_expTaylor_le _ η hεx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
