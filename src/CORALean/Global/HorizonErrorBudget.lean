import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Tactic.Positivity

/-!
# `Prop. 2`: a particular-solution error budget over a fixed horizon

[1, Prop. 2]: if `ε_P` decreases superlinearly (Def. 1), for any `ε_{P,max}>0`
there is a sequence of time intervals whose errors sum below it. [1]'s own
proof needs more than `SuperlinearDecrease` supplies: read at one reference
length, that predicate only bounds `ε_P(Δt)` by the *line through*
`(Δt_ref, ε_P(Δt_ref))`, which a linear `ε_P` already satisfies with equality —
so no plain reading of Def. 1 rules out a fixed positive limit for
`ε_P(Δt)/Δt` as `Δt→0`, and no `ε_{P,max}` budget could then be met. What the
construction below needs, and what [1]'s "superlinear" has to mean for its own
claim to hold, is `ε_P(Δt)/Δt → 0` — `Assumption 1`'s convergence, of the
*ratio* rather than of `ε_P` itself.

Proved over a fixed horizon `t_f`, covered by finitely many steps summing to it
exactly: the reading `Thm. 1` needs, not the weaker "some sequence exists, of
whatever total length", which `Assumption 1` alone already gives for free and
which is not the claim at stake here.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter Topology


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Unwinds `Tendsto` at `𝓝[>] 0` into a genuine punctured-interval bound: past
a ratio's limit, an explicit threshold beats any target. -/
theorem aux_horizonErrorBudget_eventually_lt {εP : ℝ → ℝ}
    (hratio : Tendsto (fun Δt => εP Δt / Δt) (𝓝[>] (0:ℝ)) (𝓝 0)) {c : ℝ} (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, 0 < x → x < δ → εP x < c * x := by -- --- PROOF ---
  have hev := hratio.eventually_lt_const hc
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  refine ⟨δ, hδpos, fun x hx0 hxδ => ?_⟩
  have hdist : dist x (0:ℝ) < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos hx0]; exact hxδ
  have hratio' : εP x / x < c := hδ hdist hx0
  rwa [div_lt_iff₀ hx0] at hratio'

/-- The index `⌈tf/Δtstar⌉₊`, split off its predecessor `M`, with the two facts
about `M` the construction needs: it undershoots `tf/Δtstar` and its successor
does not. -/
theorem aux_horizonErrorBudget_ceilPred {tf Δtstar : ℝ} (htf : 0 < tf) (hΔtstar : 0 < Δtstar) :
    ∃ M : ℕ, (M : ℝ) < tf / Δtstar ∧ tf / Δtstar ≤ (M : ℝ) + 1 := by -- --- PROOF ---
  set N := ⌈tf / Δtstar⌉₊ with hN_def
  have hN_pos : 0 < N := by
    rw [hN_def]; exact Nat.ceil_pos.mpr (div_pos htf hΔtstar)
  refine ⟨N - 1, ?_, ?_⟩
  · have h : N - 1 < N := by omega
    rw [hN_def] at h
    exact_mod_cast Nat.lt_ceil.mp h
  · have h : tf / Δtstar ≤ (N : ℝ) := by rw [hN_def]; exact Nat.le_ceil _
    have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
      have : N - 1 + 1 = N := by omega
      exact_mod_cast this
    linarith [hcast]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2]: a finite partition of `[0,t_f]`, of `M+1` steps, whose
`ε_P`-errors sum below any given `ε_{P,max}`. -/
theorem exists_finPartition_sum_particularError_le
    (εP : ℝ → ℝ) (hεP_ratio : Tendsto (fun Δt => εP Δt / Δt) (𝓝[>] (0:ℝ)) (𝓝 0))
    {tf : ℝ} (htf : 0 < tf) {εPmax : ℝ} (hεPmax : 0 < εPmax) :
    ∃ (M : ℕ) (Δt : Fin (M + 1) → ℝ), (∀ i, 0 < Δt i) ∧ (∑ i, Δt i = tf) ∧
      (∑ i, εP (Δt i) ≤ εPmax) := by -- --- PROOF ---
  set c := εPmax / tf with hc_def
  have hc : 0 < c := div_pos hεPmax htf
  obtain ⟨δ, hδpos, hδ⟩ := aux_horizonErrorBudget_eventually_lt hεP_ratio hc
  set Δtstar := δ / 2 with hΔtstar_def
  have hΔtstar_pos : 0 < Δtstar := by positivity
  have hΔtstar_lt_δ : Δtstar < δ := by rw [hΔtstar_def]; linarith
  obtain ⟨M, hM_lt, hM_ge⟩ := aux_horizonErrorBudget_ceilPred htf hΔtstar_pos
  have hlast_pos : 0 < tf - (M : ℝ) * Δtstar := by
    have h := mul_lt_mul_of_pos_right hM_lt hΔtstar_pos
    rw [div_mul_cancel₀ tf hΔtstar_pos.ne'] at h
    linarith
  have hlast_le : tf - (M : ℝ) * Δtstar ≤ Δtstar := by
    have h := mul_le_mul_of_nonneg_right hM_ge hΔtstar_pos.le
    rw [div_mul_cancel₀ tf hΔtstar_pos.ne'] at h
    nlinarith [h]
  -- the partition: `M` steps of the fixed length `Δtstar`, then whatever remains
  set Δt : Fin (M + 1) → ℝ :=
    fun i => if (i : ℕ) < M then Δtstar else tf - (M : ℝ) * Δtstar with hΔt_def
  -- every non-last step sits at the fixed length, the last one at what remains
  have hmid : ∀ i : Fin M, Δt i.castSucc = Δtstar := by
    intro i
    simp only [hΔt_def, Fin.val_castSucc]
    rw [if_pos i.isLt]
  have hlast : Δt (Fin.last M) = tf - (M : ℝ) * Δtstar := by
    simp only [hΔt_def, Fin.val_last]
    rw [if_neg (lt_irrefl M)]
  refine ⟨M, Δt, ?_, ?_, ?_⟩
  · intro i
    simp only [hΔt_def]
    split
    · exact hΔtstar_pos
    · exact hlast_pos
  -- the `M` fixed steps and the remainder telescope back to `tf`
  · rw [Fin.sum_univ_castSucc, Finset.sum_congr rfl fun i _ => hmid i, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, hlast, nsmul_eq_mul]
    ring
  -- each step, fixed or remainder, is short enough for `hδ` to bound its error by `c` times itself
  · have hmid_bound : εP Δtstar ≤ c * Δtstar :=
      (hδ Δtstar hΔtstar_pos hΔtstar_lt_δ).le
    have hlast_bound : εP (tf - (M : ℝ) * Δtstar) ≤ c * (tf - (M : ℝ) * Δtstar) :=
      (hδ _ hlast_pos (lt_of_le_of_lt hlast_le hΔtstar_lt_δ)).le
    calc ∑ i, εP (Δt i)
        = (∑ i : Fin M, εP (Δt i.castSucc)) + εP (Δt (Fin.last M)) :=
          Fin.sum_univ_castSucc (fun i => εP (Δt i))
      _ = (∑ _i : Fin M, εP Δtstar) + εP (tf - (M : ℝ) * Δtstar) := by
          rw [Finset.sum_congr rfl fun i _ => by rw [hmid i], hlast]
      _ ≤ (∑ _i : Fin M, c * Δtstar) + c * (tf - (M : ℝ) * Δtstar) :=
          add_le_add (Finset.sum_le_sum fun i _ => hmid_bound) hlast_bound
      _ = c * ((M : ℝ) * Δtstar + (tf - (M : ℝ) * Δtstar)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ = c * tf := by ring
      _ = εPmax := by rw [hc_def, div_mul_cancel₀ εPmax htf.ne']

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
