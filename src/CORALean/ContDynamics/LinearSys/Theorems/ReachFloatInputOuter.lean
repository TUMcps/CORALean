import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatInputInvariant
import CORALean.ContDynamics.LinearSys.Theorems.TrajectorySubMemInputReachRecentre

/-!
# `reachFloatInput` holds every run over every window

A run of `ẋ = Ax + u` with `u(t) ∈ B U`, any such signal the run is a solution
for, at `t = t_k + τ` of window `k`: its free motion plus the constant's
contribution is in `H(τ_k)`, and the rest is one `Ũ`-input's contribution by
`t` (`Trajectory.sub_mem_inputReach_recentre`), which is in `P^R(t_{k+1})`
since `0 ∈ Ũ` lets the later window end bound it (`inputReach_mono`). No
`0 ∈ U` is asked: the split took the centre out.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every run on `[0, tFinal - tStart]` from `X₀` under inputs `u(t) ∈ B U` is,
at every time of window `k`, in the `k`-th time-interval set. -/
theorem LinearSys.reachFloatInput_outer (sys : LinearSys 𝕋 n) (B : Mat 𝕋 n m)
    {params : Reach.InputParams (Zonotope 𝕋 n) (Zonotope 𝕋 m) ℚ}
    {options : LinearSys.ReachOptions 𝕋} {Rti Rtp : List (Zonotope 𝕋 n)}
    (h : sys.reachFloatInput B params options = some (Rti, Rtp)) :
    ∃ N : ℕ, (N : ℝ) * toReal options.timeStep = (params.tFinal : ℝ) - params.tStart ∧
      Rti.length = N ∧ ∀ {x u : ℝ → Vec ℝ n},
        sys.Trajectory (S := fun k => Set (Vec ℝ k))
          (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart)) params.R0.construct
          ((Scalar.toRealMat B *ᵥ ·) '' params.U.construct) x u →
        ∀ (k : ℕ) (hk : k < Rti.length), ∀ t ∈ Set.Icc ((k : ℝ) * toReal options.timeStep)
          (((k : ℝ) + 1) * toReal options.timeStep), x t ∈ Rti[k].construct := by -- --- PROOF ---
  obtain ⟨hΔt, N, hNΔt, S, hlen, rfl, rfl, hinv⟩ := sys.reachFloatInput_invariant B h
  refine ⟨N, hNΔt, by simp [hlen], fun {x u} traj k hk t ht => ?_⟩
  set Δ := toReal options.timeStep with hΔ
  set V := Mtimes.mtimes (𝕄 := Mat 𝕋) B params.U with hV
  have hk' : k < S.length := by simpa using hk
  obtain ⟨-, h2, h3, -⟩ := hinv k hk'
  -- the run's inputs are in `B U`'s float enclosure
  have hUV : ContSet.construct ((Scalar.toRealMat B *ᵥ ·) '' params.U.construct)
      ⊆ ContSet.construct V := by
    rintro _ ⟨w, hw, rfl⟩
    exact Mtimes.mtimes_outer (𝕄 := Mat 𝕋) B params.U
      (Set.mem_biUnion (Set.mem_singleton _) (Set.mem_image_of_mem _ hw))
  -- window `k` lies inside the horizon
  have hkN : ((k : ℝ) + 1) * Δ ≤ (params.tFinal : ℝ) - params.tStart := by
    rw [← hNΔt]
    have : (k : ℝ) + 1 ≤ N := by rw [← hlen]; exact_mod_cast hk'
    exact mul_le_mul_of_nonneg_right this hΔt.le
  have ht0 : 0 ≤ t := le_trans (by positivity) ht.1
  have hd := traj.sub_mem_inputReach_recentre hUV ⟨ht0, ht.2.trans hkN⟩
  -- the `Ũ`-input's share by `t`, inside `P^R(t_{k+1})`
  have hy := h3 (sys.inputReach_mono (CompactSet.isBounded_construct _)
    (Recentre.zero_mem_recentre _) ht0 (by push_cast; exact ht.2) hd)
  -- the free motion and the constant's share at `t = t_k + τ`, inside `H(τ_k)`
  have hx := h2 (x 0) traj.init (t - k * Δ) ⟨sub_nonneg.mpr ht.1, by linarith [ht.2]⟩
  rw [add_sub_cancel] at hx
  rw [List.getElem_map]
  have hsum := Plus.plus_outer S[k].2.1 S[k].2.2.1 (Set.add_mem_add hx hy)
  rwa [add_sub_cancel] at hsum

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
