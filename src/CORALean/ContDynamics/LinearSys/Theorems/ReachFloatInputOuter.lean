module

public import CORALean.ContDynamics.LinearSys.Theorems.InputSetFloatOuter
public import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatInputInvariant
public import CORALean.ContDynamics.LinearSys.Theorems.TrajectorySubMemInputReachRecentre

@[expose] public section

/-!
# `reachFloatInput` holds every run over every window

A run of `ẋ = Ax + u` with `u(t) ∈ B U + c`, any such signal the run is a solution
for, at `t = t_k + τ` of window `k`: its free motion plus the constant's
contribution is in `H(τ_k)`, and the rest is one `Ũ`-input's contribution by
`t` (`Trajectory.sub_mem_inputReach_recentre`), which is in `P^R(t_{k+1})`
since `0 ∈ Ũ` lets the later window end bound it (`inputReach_mono`). No
`0 ∈ U` is asked: the split took the centre out.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every run on `[0, tFinal - tStart]` from `X₀` under inputs `u(t) ∈ B U + c` is,
at every time of window `k`, in the `k`-th time-interval set. -/
theorem LinearSys.reachFloatInput_outer (sys : LinearSys 𝕋 n)
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 sys.m)) ℚ}
    {options : LinearSys.ReachOptions 𝕋} {Rti Rtp : List (Zonotope (Vec 𝕋 n))}
    (h : sys.reachFloatInput params options = some (Rti, Rtp)) :
    ∃ N : ℕ, (N : ℝ) * toReal options.Δt = (params.tFinal : ℝ) - params.tStart ∧
      Rti.length = N ∧ ∀ {x u : ℝ → Vec ℝ n},
        sys.CanonicalTrajectory (S := 𝒮)
          (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart)) params.X₀.construct
          ((fun u => Scalar.toRealMat sys.B *ᵥ u + Scalar.toRealVec sys.c) ''
            params.U.construct) x u →
        ∀ (k : ℕ) (hk : k < Rti.length), ∀ t ∈ Set.Icc ((k : ℝ) * toReal options.Δt)
          (((k : ℝ) + 1) * toReal options.Δt), x t ∈ Rti[k].construct := by -- --- PROOF ---
  obtain ⟨hΔt, N, hNΔt, S, hlen, rfl, rfl, hinv⟩ := sys.reachFloatInput_invariant h
  refine ⟨N, hNΔt, by simp [hlen], fun {x u} traj k hk t ht => ?_⟩
  set Δ := toReal options.Δt with hΔ
  set V := sys.inputSetFloat params.U with hV
  have hk' : k < S.length := by simpa using hk
  obtain ⟨-, h2, h3, -⟩ := hinv k hk'
  -- the run's inputs `B u + c` are in `B U ⊕ c`'s float enclosure
  have hUV : (fun u => Scalar.toRealMat sys.B *ᵥ u + Scalar.toRealVec sys.c) ''
      params.U.construct ⊆ ContSet.construct V :=
    sys.inputSetFloat_outer params.U
  -- window `k` lies inside the horizon
  have hkN : ((k : ℝ) + 1) * Δ ≤ (params.tFinal : ℝ) - params.tStart := by
    rw [← hNΔt]
    have : (k : ℝ) + 1 ≤ N := by rw [← hlen]; exact_mod_cast hk'
    exact mul_le_mul_of_nonneg_right this hΔt.le
  have ht0 : 0 ≤ t := le_trans (by positivity) ht.1
  have hd := traj.sub_mem_inputReach_recentre (S' := 𝒵[𝕋]) hUV
    ⟨ht0, ht.2.trans hkN⟩
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
