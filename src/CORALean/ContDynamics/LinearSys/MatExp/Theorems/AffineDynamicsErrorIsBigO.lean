module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoAffineDynamicsErrorZero

@[expose] public section

/-!
# `Lemma 3`, the rate half: `Δε^h_k(Δt,η) ∼ O(Δt)` as `Δt → 0⁺`

[1, Lemma 3]: `exists_affineDynamicsError_le_const_mul`'s eventual linear bound is exactly an
`IsBigO` witness once its constant is read at `|K|`.

`O(Δt)` and not better: the curvature term `2·err(C)` is `O(Δt²)` whenever `η ≥ 1`, but
`‖G^{(-)}_h‖₂ = ‖(e^{AΔt} - I)G_h‖₂` is only linear, and it is what the rate is.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
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

/-- [1, Lemma 3], the rate half: `Δε^h_k(Δt,η)` is `O(Δt)` as the step shrinks to `0`. -/
theorem MatExp.affineDynamicsError_isBigO (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (η : ℕ) :
    (fun Δt => MatExp.affineDynamicsError A H ũ Δt η)
      =O[𝓝[>] (0 : ℝ)] fun Δt : ℝ => Δt := by -- --- PROOF ---
  obtain ⟨K, hK⟩ := MatExp.exists_affineDynamicsError_le_const_mul A H ũ η
  refine IsBigO.of_bound |K| ?_
  filter_upwards [hK, self_mem_nhdsWithin] with Δt hK hΔtmem
  have hΔtpos : (0:ℝ) < Δt := hΔtmem
  have hnn : (0:ℝ) ≤ MatExp.affineDynamicsError A H ũ Δt η :=
    MatExp.affineDynamicsError_nonneg A H ũ Δt η
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_pos hΔtpos]
  exact hK.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hΔtpos.le)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
