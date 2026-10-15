module

public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachInnerCert
public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachInner
public import CORALean.ContDynamics.NonlinearSys.Theorems.MinkowskiDiffAddSubsetReachSet

@[expose] public section

/-!
# CORA's inner linearized step: the time-point set is inside the reachable set

The time-point set `Rtp.set = minkDiff(Rlintp__ + p, Rerror)` CORA's
`contDynamics/linReachInner.m` computes from `X = Rinit`, with the exact Minkowski difference,
holds only states some run from `X` reaches at `Δt`, given [1, Prop. 1]'s hypotheses for the
step (`LinReachInnerCert`). This is `NonlinearSys.minkowskiDiff_add_subset_reachSet` with the
center `c = 0` (CORA's `Rerror` is symmetric about the origin, so `Prop. 1`'s shift `2c`
vanishes) and `Rlintp__ + p` written as the image of the affine map
`x₀ ↦ e^{AΔt}x₀ + (p - e^{AΔt}p + Rcon)`, its matrix invertible.

The input is the constant `u₀`, `U = {u₀}`, CORA's `params.u`.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Matrix NormedSpace Set

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ} {𝓛 : Type}


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `linReachInner`: `Rtp.set ⊆ R(Δt)` from `X = Rinit`, given `Prop. 1`'s hypotheses. -/
theorem NonlinearSys.linReachInner_subset_reachSet (ops : NonlinearSys.LinReachInnerOps n 𝓛)
    (sys : NonlinearSys n m) (u₀ : Vec ℝ m) {Δt : ℝ} (hΔt : 0 ≤ Δt) (fuel : ℕ)
    {X : Set (Vec ℝ n)} {e : Vec ℝ n} {st : NonlinearSys.LinReachInnerState n 𝓛}
    (h : NonlinearSys.linReachInner ops (fun x => sys.f x u₀) Δt fuel X e = some (some st))
    (cert : NonlinearSys.LinReachInnerCert sys u₀ Δt X st) :
    st.Rtp ⊆ sys.reachSet (S := 𝒮) (Icc 0 Δt) X {u₀}
      Δt := by -- --- PROOF ---
  -- what `Rtp.set` and `Rlintp__ + p` are
  have hst : st.Rtp = minkowskiDiff st.Rlintp st.Rerror ∧
      st.Rlintp = (fun x => x + st.p) '' ((fun x => exp (Δt • st.A) *ᵥ x + st.Rcon) ''
        ((fun x => x - st.p) '' X)) := by
    unfold NonlinearSys.linReachInner at h
    dsimp only at h
    split_ifs at h
    · simp at h
    obtain ⟨_, -, hr⟩ := Option.map_eq_some_iff.mp h
    obtain rfl := Option.some.inj hr
    exact ⟨rfl, rfl⟩
  set M := exp (Δt • st.A)
  set v := st.p - M *ᵥ st.p + st.Rcon
  have hR : st.Rlintp = (fun x₀ => M *ᵥ x₀ + v) '' X := by
    rw [hst.2, image_image, image_image]
    refine image_congr fun x _ => ?_
    simp only [v, Matrix.mulVec_sub]
    abel
  -- `Prop. 1` for the affine map at the center `0`, (21) rewritten about `p`
  obtain ⟨Ω, K, hLip, hex⟩ := cert.flow
  have key := NonlinearSys.minkowskiDiff_add_subset_reachSet (S := 𝒮) sys
    X {u₀} hΔt M ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)) v cert.compact
    cert.convex cert.nonempty (c := 0)
    (fun e he => by rw [smul_zero, zero_sub]; exact cert.symm e he) (mem_singleton u₀) hLip hex
    fun x₀ hx₀ x hx0 hder => by
      have hv : M *ᵥ x₀ + v = st.p + M *ᵥ (x₀ - st.p) + st.Rcon := by
        simp only [v, Matrix.mulVec_sub]
        abel
      rw [hv]
      exact cert.err x₀ hx₀ x hx0 hder
  simp only [smul_zero, add_zero, image_id'] at key
  rw [hst.1, hR]
  exact key

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
