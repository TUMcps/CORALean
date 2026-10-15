module

public import CORALean.ContDynamics.LinearSys.Theorems.InputSetFloatOuter
public import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatInputInvariant
public import CORALean.ContDynamics.LinearSys.Theorems.TrajectorySubMemInputReachRecenter
public import CORALean.ContSet.ContSet.Theorems.Basic

@[expose] public section

/-!
# `reachFloatInput`'s time-point sets hold every run at `t_k`

`R_0 = X₀` holds `x(0)`; at `t_{k+1}` the free motion plus the constant's
contribution is in `H(t_{k+1})`, and the rest is one `Ũ`-input's contribution
by `t_{k+1}` (`Trajectory.sub_mem_inputReach_recenter`), in `P^R(t_{k+1})`.
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

/-- Every run on `[0, tFinal - tStart]` from `X₀` under inputs `u(t) ∈ B U + c` is
at `t_k = k Δt` in the `k`-th time-point set. -/
theorem LinearSys.reachFloatInput_timePoint_outer (sys : LinearSys 𝕋 n)
    {params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 sys.m)) ℚ}
    {options : LinearSys.ReachOptions 𝕋} {Rti Rtp : List (Zonotope (Vec 𝕋 n))}
    (h : sys.reachFloatInput params options = some (Rti, Rtp)) :
    ∃ N : ℕ, (N : ℝ) * toReal options.Δt = (params.tFinal : ℝ) - params.tStart ∧
      Rtp.length = N + 1 ∧ ∀ {x u : ℝ → Vec ℝ n},
        sys.CanonicalTrajectory (S := 𝒮)
          (Set.Icc 0 ((params.tFinal : ℝ) - params.tStart)) params.X₀.construct
          ((fun u => Scalar.toRealMat sys.B *ᵥ u + Scalar.toRealVec sys.c) ''
            params.U.construct) x u →
        ∀ (k : ℕ) (hk : k < Rtp.length),
          x ((k : ℝ) * toReal options.Δt) ∈ Rtp[k].construct := by -- --- PROOF ---
  obtain ⟨hΔt, N, hNΔt, S, hlen, rfl, rfl, hinv⟩ := sys.reachFloatInput_invariant h
  refine ⟨N, hNΔt, by simp [hlen], fun {x u} traj k hk => ?_⟩
  cases k with
  | zero =>
    -- `R_0 = X₀`
    simpa using traj.init
  | succ k =>
    set Δ := toReal options.Δt with hΔ
    set V := sys.inputSetFloat params.U with hV
    have hk' : k < S.length := by simpa using hk
    obtain ⟨h1, -, h3, -⟩ := hinv k hk'
    -- the run's inputs `B u + c` are in `B U ⊕ c`'s float enclosure
    have hUV : (fun u => Scalar.toRealMat sys.B *ᵥ u + Scalar.toRealVec sys.c) ''
        params.U.construct ⊆ ContSet.construct V :=
      sys.inputSetFloat_outer params.U
    -- `t_{k+1}` lies inside the horizon
    have hkN : ((k + 1 : ℕ) : ℝ) * Δ ≤ (params.tFinal : ℝ) - params.tStart := by
      rw [← hNΔt]
      have : ((k + 1 : ℕ) : ℝ) ≤ N := by rw [← hlen]; exact_mod_cast hk'
      exact mul_le_mul_of_nonneg_right this hΔt.le
    have hd := traj.sub_mem_inputReach_recenter (S' := 𝒵[𝕋]) hUV
      ⟨by positivity, hkN⟩
    have hsum := Plus.plus_outer S[k].1 S[k].2.2.1 (Set.add_mem_add (h1 (x 0) traj.init) (h3 hd))
    rw [add_sub_cancel] at hsum
    simp only [List.getElem_cons_succ, List.getElem_map]
    exact hsum

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
