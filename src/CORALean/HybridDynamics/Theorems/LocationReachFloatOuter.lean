import CORALean.ContDynamics.LinearSys.Theorems.ClassicalTrajectoryTrajectory
import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
import CORALean.ContDynamics.LinearSys.Theorems.ReachFloatInputInvariant
import CORALean.ContDynamics.LinearSys.Theorems.TrajectorySubMemInputReachRecentre
import CORALean.HybridDynamics.Operations.LocationReachFloat
import CORALean.HybridDynamics.Theorems.LinearEmbedding

/-!
# `Location.reachFloat` holds every stay of length up to `tFinal`

`LinearSys.reachFloatInput_outer`, read at a stay rather than at a run over the
whole horizon: the windows' enclosures are statements about states, not about
trajectories, so a stay of length `τ ≤ tFinal` is held at each of its times
`t` by the window `k` with `t ∈ [k Δt, (k + 1) Δt]`. The location's inputs lie
in `ℓ.U`, and so in the identity's image of it.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic NormedSpace Matrix ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
variable {G : ℕ → Type} [∀ n, ContSet (G n) (Vec ℝ n)]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A time of the horizon `[0, N Δ]`, `N ≥ 1`, lies in one of its `N` windows. -/
theorem aux_window {N : ℕ} {Δ t : ℝ} (hΔ : 0 < Δ) (hN : 0 < N) (ht0 : 0 ≤ t)
    (htN : t ≤ N * Δ) : ∃ k < N, (k : ℝ) * Δ ≤ t ∧ t ≤ ((k : ℝ) + 1) * Δ := by -- --- PROOF ---
  have hq : 0 ≤ t / Δ := div_nonneg ht0 hΔ.le
  by_cases hk : ⌊t / Δ⌋₊ < N
  · refine ⟨⌊t / Δ⌋₊, hk, ?_, ?_⟩
    · exact (le_div_iff₀ hΔ).mp (Nat.floor_le hq)
    · exact ((div_le_iff₀ hΔ).mp (Nat.lt_floor_add_one (t / Δ)).le)
  · -- past the last window's start, so in the last window
    refine ⟨N - 1, Nat.sub_lt hN one_pos, ?_, ?_⟩
    · have hNt : (N : ℝ) * Δ ≤ t :=
        (le_div_iff₀ hΔ).mp (le_trans (by exact_mod_cast not_lt.mp hk) (Nat.floor_le hq))
      have : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
      nlinarith
    · rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hN.ne'), Nat.cast_one, sub_add_cancel]
      exact htN


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state a stay of length `τ ≤ tFinal` from `X₀` passes through lies in
one of the computed time-interval sets. -/
theorem Location.Trajectory.reachFloat_outer
    {ℓ : Location (fun k => Zonotope (Vec 𝕋 k)) G L 𝕋 n} {τ : ℝ}
    {x u : ℝ → Vec ℝ n} (traj : ℓ.Trajectory τ x u) {tFinal : ℚ}
    {options : LinearSys.ReachOptions 𝕋} {X₀ : Zonotope (Vec 𝕋 n)} {Rs : List (Zonotope (Vec 𝕋 n))}
    (h : ℓ.reachFloat tFinal options X₀ = some Rs) (h₀ : x 0 ∈ construct X₀)
    (hτ : τ ≤ tFinal) {t : ℝ} (ht : t ∈ Set.Icc 0 τ) :
    ∃ R ∈ Rs, x t ∈ construct R := by -- --- PROOF ---
  unfold Location.reachFloat at h
  split_ifs at h with htf
  obtain ⟨⟨Rti, Rtp⟩, hreach, hRs⟩ := Option.bind_eq_some_iff.mp h
  cases hRs
  obtain ⟨hΔt, N, hNΔt, S, hlen, rfl, -, hinv⟩ :=
    ℓ.dynamics.reachFloatInput_invariant (identityMat 𝕋 n) hreach
  set Δ := toReal options.timeStep with hΔ
  set V := Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k))
    (identityMat 𝕋 n) ℓ.U with hV
  simp only [Rat.cast_zero, sub_zero] at hNΔt
  -- the horizon holds `t`, and has at least one window
  have htf' : (0 : ℝ) < tFinal := by exact_mod_cast not_le.mp htf
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0, Nat.cast_zero, zero_mul] at hNΔt
      linarith
    · exact h0
  obtain ⟨k, hk, hkt, htk⟩ := aux_window hΔt hN ht.1 (by rw [hNΔt]; linarith [ht.2])
  have hk' : k < S.length := by rw [hlen]; exact hk
  obtain ⟨-, h2, h3, -⟩ := hinv k hk'
  -- the location's inputs are in the identity's image of `ℓ.U`
  have hUV : construct ℓ.U ⊆ construct V := by
    intro w hw
    have hI : toRealMat (identityMat 𝕋 n) *ᵥ w = w := funext (identityMat_mulVec w)
    rw [← hI]
    exact Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (S := fun k => Zonotope (Vec 𝕋 k)) (identityMat 𝕋 n) ℓ.U
      (Set.mem_biUnion (Set.mem_singleton _) (Set.mem_image_of_mem _ hw))
  have hd := ((traj.linearSys h₀).trajectory (convex_Icc 0 τ) ⟨le_rfl, ht.1.trans ht.2⟩
    (CompactSet.isBounded_construct ℓ.U)).sub_mem_inputReach_recentre
      (S' := fun k => Zonotope (Vec 𝕋 k)) hUV ht
  -- the `Ũ`-input's share by `t`, inside `P^R(t_{k+1})`
  have hy := h3 (ℓ.dynamics.inputReach_mono (CompactSet.isBounded_construct _)
    (Recentre.zero_mem_recentre _) ht.1 (by push_cast; exact htk) hd)
  -- the free motion and the constant's share at `t = t_k + (t - t_k)`, inside `H(τ_k)`
  have hx := h2 (x 0) h₀ (t - k * Δ) ⟨sub_nonneg.mpr hkt, by linarith⟩
  rw [add_sub_cancel] at hx
  refine ⟨_, List.getElem_mem (l := S.map fun s => s.2.1 ⊞ s.2.2.1) (by simpa using hk'), ?_⟩
  rw [List.getElem_map]
  have hsum := Plus.plus_outer S[k].2.1 S[k].2.2.1 (Set.add_mem_add hx hy)
  rwa [add_sub_cancel] at hsum

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
