module

public import CORALean.ContDynamics.NonlinearSys.Definitions.IsInnerMinkDiffCert
public import CORALean.ContDynamics.NonlinearSys.Operations.InnerMinkDiffStep
public import CORALean.ContDynamics.NonlinearSys.Theorems.MinkowskiDiffAddSubsetReachSetExact

@[expose] public section

/-!
# One step of the inner algorithm stays inside the reachable set

Line 15 of [1, Alg. 1]: the time-point set `R̂(t_{k+1}) = R_aff(Δt) ⊖ R̂_err(L̂) + 2c` a step
computes from `X = R̂(t_k)` holds only states some run from `X` reaches at `Δt`, given
[1, Prop. 1]'s hypotheses for the step (`IsInnerMinkDiffCert`). This is
`NonlinearSys.minkowskiDiff_add_subset_reachSetExact` with `R_aff(Δt)` written as the image of the
affine map `x₀ ↦ e^{AΔt}x₀ + (x* - e^{AΔt}x* + R_con(Δt))`, its matrix invertible.

The input is the constant `u₀`, `U = {u₀}`, the autonomous system (4) of [1].

## Inputs
* `ops` – set operations
* `sys` – system
* `u₀` – constant input
* `Δt` – step size
* `μ` – enlargement factor
* `fuel` – bound per remainder loop
* `X` – start set

## Hypotheses
* `hΔt` – step size nonnegative

## Conclusion
* the next time-point set lies in the exact reachable set

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
      2024.](../../../../../references/2024/wetzlinger-lcss-inner-minkowski-difference.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Matrix NormedSpace Set

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ} {𝓛 : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Alg. 1] line 15: `R̂(t_{k+1}) ⊆ R(Δt)` from `X = R̂(t_k)`, given `Prop. 1`'s hypotheses. -/
theorem NonlinearSys.innerMinkDiffStep_subset_reachSetExact
    (ops : NonlinearSys.InnerMinkDiffOps n 𝓛) (sys : NonlinearSys n m) (u₀ : Vec ℝ m) {Δt : ℝ}
    (hΔt : 0 ≤ Δt) (μ : ℝ) (fuel : ℕ) {X : Set (Vec ℝ n)} : -- --- CONCL ---
    ∀ st ∈ NonlinearSys.innerMinkDiffStep ops (fun x => sys.f x u₀) Δt μ fuel X,
      NonlinearSys.IsInnerMinkDiffCert sys u₀ Δt X st →
      st.Rtk1 ⊆ sys.reachSetExact (S := 𝒮) (Icc 0 Δt) X {u₀}
        Δt := by -- --- PROOF ---
  intro st (h : NonlinearSys.innerMinkDiffStep ops (fun x => sys.f x u₀) Δt μ fuel X = some st) cert
  -- what line 15 and lines 7-8 computed
  have hst : st.Rtk1 = (fun x => x + (2 : ℝ) • st.c) '' minkowskiDiff st.Raff st.Rerr ∧
      st.Raff = (fun x => x + st.Rcon) ''
        ((fun x => st.xstar + exp (Δt • st.A) *ᵥ (x - st.xstar)) '' X) := by
    unfold NonlinearSys.innerMinkDiffStep at h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, rfl⟩
  set M := exp (Δt • st.A)
  set v := st.xstar - M *ᵥ st.xstar + st.Rcon
  have hRaff : st.Raff = (fun x₀ => M *ᵥ x₀ + v) '' X := by
    rw [hst.2, image_image]
    refine image_congr fun x _ => ?_
    simp only [v, Matrix.mulVec_sub]
    abel
  -- `Prop. 1` for the affine map, (21) rewritten about `x*`
  obtain ⟨Ω, K, hLip, hex⟩ := cert.flow
  rw [hst.1, hRaff]
  refine NonlinearSys.minkowskiDiff_add_subset_reachSetExact (S := 𝒮) sys X {u₀}
    hΔt M
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)) v cert.compact cert.convex
    cert.nonempty cert.symm (mem_singleton u₀) hLip hex fun x₀ hx₀ x hx0 hder => ?_
  have e := cert.err x₀ hx₀ x hx0 hder
  have hv : M *ᵥ x₀ + v = st.xstar + M *ᵥ (x₀ - st.xstar) + st.Rcon := by
    simp only [v, Matrix.mulVec_sub]
    abel
  rw [hv]
  exact e

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
