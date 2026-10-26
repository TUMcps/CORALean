module

public import CORALean.ContDynamics.LinearSys.Operations.AutoTuneDeltaT
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ParticularSolutionErrorIsBigO
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoAffineDynamicsErrorZero
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.TendstoParticularSolutionTauErrorZero
public import CORALean.ContSet.Zonotope.Real.Theorems.IsBounded

@[expose] public section

/-!
# `Thm. 1`: `Alg. 2` lines 5-15 always land, for every `ε_max > 0`

[1, Thm. 1]'s own two-sentence argument, against the search this tree computes. The accumulating
error `Δε^a_k` is `O(Δt²)` (`Lemma 2`) while its admissible share `ε^{a,τ}_k` (eq. 37) falls only
*linearly* with `Δt`, provided what is already accumulated is inside eq. (36)'s share at `t_k`, the
one carried hypothesis, so halving eventually clears it. The non-accumulating error `Δε^n_k`
vanishes (`Lemma 3`, `Lemma 4`) while its share `ε^{n,τ}_k` (eq. 38) approaches a *positive*
constant, `t_k < t_end` making it positive. Not formalizable here is [1]'s word "terminates": its
`Δt_k` loop searches without a bound, ours takes a `fuel` and returns `Option`, so it terminates by
construction; what transfers is that the search is not vacuous. The check must be complete here.

## Inputs
* `sys` – linear system
* `le` – comparison oracle on reals
* `H` – state zonotope
* `ũ` – constant input
* `U₀` – recentered input zonotope
* `tk` – step start time
* `tend` – final time
* `εmax` – admissible error
* `ζ` – error budget share
* `εaAcc` – accumulated approximation error
* `Δtprev` – previous step length
* `ηmax` – maximal Taylor order

## Hypotheses
* `hle` – comparison oracle is complete
* `htend` – step start before the final time
* `htpos` – final time positive
* `hεmax` – admissible error positive
* `hζ1` – error share below one
* `hacc` – accumulated error within its share
* `hΔtprev` – previous step positive
* `hηmax` – maximal order at least one

## Conclusion
* some fuel makes the step-size search report a positive step

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Scalar Filter Topology

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `Lemma 2` against eq. (37): a quadratic error eventually fits under a share that falls
only linearly, once eq. (36) puts what is already accumulated inside its own share. -/
private theorem aux_eventually_particularSolutionError_le (A : Mat ℝ n n) (tk : ℝ)
    {U0 : Set (Vec ℝ n)} (hU0 : Bornology.IsBounded U0) (η : ℕ) {tend εmax ζ εaAcc : ℝ}
    (htend : 0 < tend) (hεmax : 0 < εmax) (hζ1 : ζ < 1)
    (hacc : εaAcc ≤ tk / tend * (1 - ζ) * εmax) : -- --- CONCL ---
    ∀ᶠ Δt : ℝ in 𝓝[>] (0 : ℝ), MatExp.particularSolutionError A tk U0 Δt η
      ≤ (tk + Δt) / tend * (1 - ζ) * εmax - εaAcc := by -- --- PROOF ---
  obtain ⟨K, hK⟩ := MatExp.exists_particularSolutionError_le_const_mul_sq A tk hU0 η
  have hc : 0 < (1 - ζ) * εmax / tend := div_pos (mul_pos (by linarith) hεmax) htend
  have hid : Tendsto (fun Δt : ℝ => Δt) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hslope : Tendsto (fun Δt : ℝ => max K 0 * Δt) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hid.const_mul (max K 0)
  filter_upwards [hK, hslope.eventually_lt_const hc, self_mem_nhdsWithin] with Δt hK hslope hmem
  have hΔt : (0 : ℝ) < Δt := hmem
  -- the share's own slope in `Δt` is what the quadratic error has to get under
  have hsplit : (tk + Δt) / tend * (1 - ζ) * εmax
      = tk / tend * (1 - ζ) * εmax + (1 - ζ) * εmax / tend * Δt := by
    field_simp
  have hsq : K * Δt ^ 2 ≤ (1 - ζ) * εmax / tend * Δt := by
    have h1 : K * Δt ^ 2 ≤ max K 0 * Δt ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left K 0) (sq_nonneg Δt)
    nlinarith [le_max_right K 0]
  linarith [hK]

/-- `Lemma 3` and `Lemma 4` against eq. (38): a vanishing error eventually fits under a
share that approaches a positive constant, `t_k < t_end` being what makes it positive. -/
private theorem aux_eventually_nonAccumulating_le (A : Mat ℝ n n) (H : Zonotope (Vec ℝ n))
    (ũ : Vec ℝ n) (tk : ℝ) {U0 : Set (Vec ℝ n)} (hU0 : Bornology.IsBounded U0) (η : ℕ)
    {tend εmax ζ εaAcc : ℝ} (htk : 0 < tend) (htend : tk < tend) (hεmax : 0 < εmax)
    (hacc : εaAcc ≤ tk / tend * (1 - ζ) * εmax) : -- --- CONCL ---
    ∀ᶠ Δt : ℝ in 𝓝[>] (0 : ℝ), MatExp.affineDynamicsError A H ũ Δt η
        + MatExp.particularSolutionTauError A tk U0 Δt η
      ≤ εmax - (tk + Δt) / tend * ζ * εmax - εaAcc := by -- --- PROOF ---
  have hid : Tendsto (fun Δt : ℝ => Δt) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hshift : Tendsto (fun Δt : ℝ => Δt * (ζ * εmax / tend)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hid.mul_const (ζ * εmax / tend)
  have hsum : Tendsto (fun Δt : ℝ => (MatExp.affineDynamicsError A H ũ Δt η
      + MatExp.particularSolutionTauError A tk U0 Δt η) + Δt * (ζ * εmax / tend))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h34 := (MatExp.tendsto_affineDynamicsError_zero A H ũ η).add
      (MatExp.tendsto_particularSolutionTauError_zero A tk hU0 η)
    simpa using h34.add hshift
  have hd : 0 < εmax * (tend - tk) / tend := by
    exact div_pos (mul_pos hεmax (by linarith)) htk
  filter_upwards [hsum.eventually_lt_const hd] with Δt hlt
  -- what the share has left over the positive constant is exactly eq. (36)'s slack
  have hkey : εmax - (tk + Δt) / tend * ζ * εmax - εaAcc
      - (εmax * (tend - tk) / tend - Δt * (ζ * εmax / tend))
    = tk / tend * (1 - ζ) * εmax - εaAcc := by field_simp; ring
  linarith

/-- The order sweep reports its coarsest candidate where that candidate's own check
clears, `1 ≤ ηmax` being what leaves it an iteration to report in. -/
private theorem aux_autoTuneOrder_exists (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (H : Zonotope (Vec ℝ n)) (ũ : Vec ℝ n) (tk : ℝ) (U₀ : Zonotope (Vec ℝ n))
    (Δt εaτ εnτ : ℝ) {ηmax : ℕ} (hηmax : 1 ≤ ηmax)
    (hc : (le (MatExp.particularSolutionError (toRealMat sys.A) tk U₀.construct Δt 2) εaτ
      && le (MatExp.affineDynamicsError (toRealMat sys.A) H ũ Δt 2
        + MatExp.particularSolutionTauError (toRealMat sys.A) tk U₀.construct Δt 2) εnτ)
      = true) : -- --- CONCL ---
    sys.autoTuneOrder le H ũ tk U₀ Δt εaτ εnτ 2 ηmax = some 2 := by -- --- PROOF ---
  obtain ⟨m, hm⟩ : ∃ m, ηmax = m + 1 := ⟨ηmax - 1, by omega⟩
  rw [hm]
  simp only [LinearSys.autoTuneOrder]
  split
  · rfl
  · rename_i hne
    exact absurd hc hne

/-- Every step the halving sweep walks is `Δt₀/2^(j+1)`, so an order clearing both shares
anywhere along that sequence is one the sweep's own fuel reaches. -/
private theorem aux_autoTuneSearch_exists (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (H : Zonotope (Vec ℝ n)) (ũ : Vec ℝ n) (tk tend εmax ζ εaAcc : ℝ) (ηmax : ℕ)
    (U₀ : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    ∀ (j : ℕ) (Δt : ℝ) (η : ℕ),
      sys.autoTuneOrder le H ũ tk U₀ (Δt / 2 ^ (j + 1))
          ((tk + Δt / 2 ^ (j + 1)) / tend * (1 - ζ) * εmax - εaAcc)
          (εmax - (tk + Δt / 2 ^ (j + 1)) / tend * ζ * εmax - εaAcc) 2 ηmax = some η →
      ∃ p, sys.autoTuneSearch le H ũ tk tend εmax ζ εaAcc ηmax U₀ Δt (j + 1)
        = some p := by -- --- PROOF ---
  intro j
  induction j with
  | zero =>
    intro Δt η h
    rw [pow_one] at h
    simp only [LinearSys.autoTuneSearch, h]
    exact ⟨(Δt / 2, η), rfl⟩
  | succ j ih =>
    intro Δt η h
    simp only [LinearSys.autoTuneSearch]
    split
    · rename_i η' _
      exact ⟨(Δt / 2, η'), rfl⟩
    -- no order cleared at this candidate, so the sweep halves again with the rest of the fuel
    · refine ih (Δt / 2) η ?_
      rwa [div_div, ← pow_succ']

/-- Every candidate the sweep can report is a halving of a positive step, so it is
positive — which is what the time `t_{k+1}` of the step after it rests on. -/
private theorem aux_autoTuneSearch_pos (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (H : Zonotope (Vec ℝ n)) (ũ : Vec ℝ n) (tk tend εmax ζ εaAcc : ℝ) (ηmax : ℕ)
    (U₀ : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    ∀ (k : ℕ) (Δt : ℝ) (p : ℝ × ℕ), 0 < Δt →
      sys.autoTuneSearch le H ũ tk tend εmax ζ εaAcc ηmax U₀ Δt k = some p →
      0 < p.1 := by -- --- PROOF ---
  intro k
  induction k with
  | zero =>
    intro Δt p _ h
    rw [LinearSys.autoTuneSearch] at h
    exact absurd h (by simp)
  | succ k ih =>
    intro Δt p hΔt h
    simp only [LinearSys.autoTuneSearch] at h
    split at h
    · rw [← Option.some.inj h]
      exact half_pos hΔt
    · exact ih (Δt / 2) p (half_pos hΔt) h


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1], the half that transfers: `Alg. 2`'s step-size search is not vacuous.
For every `ε_max > 0` some fuel is enough, and the step it reports is positive. -/
theorem LinearSys.exists_autoTuneDeltaT (sys : LinearSys 𝕋 n) {le : ℝ → ℝ → Bool}
    (hle : ∀ a b : ℝ, a ≤ b → le a b = true) (H : Zonotope (Vec ℝ n)) (ũ : Vec ℝ n)
    (U₀ : Zonotope (Vec ℝ n)) {tk tend εmax ζ εaAcc Δtprev : ℝ} {ηmax : ℕ}
    (htend : tk < tend) (htpos : 0 < tend) (hεmax : 0 < εmax) (hζ1 : ζ < 1)
    (hacc : εaAcc ≤ tk / tend * (1 - ζ) * εmax) (hΔtprev : 0 < Δtprev)
    (hηmax : 1 ≤ ηmax) : -- --- CONCL ---
    ∃ (fuel : ℕ) (Δt : ℝ) (η : ℕ),
      sys.autoTuneDeltaT le H ũ tk tend εmax ζ εaAcc Δtprev ηmax fuel U₀ = some (Δt, η)
        ∧ 0 < Δt := by -- --- PROOF ---
  have hΔt₀ : (0 : ℝ) < 2 * Δtprev := by linarith
  -- the halvings reach into the punctured neighbourhood both convergence facts live over
  have hseq : Tendsto (fun j : ℕ => 2 * Δtprev / 2 ^ (j + 1)) atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hpow : Tendsto (fun j : ℕ => ((1 : ℝ) / 2) ^ j) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have hfun : (fun j : ℕ => 2 * Δtprev / 2 ^ (j + 1))
          = fun j : ℕ => Δtprev * ((1:ℝ)/2) ^ j := by
        funext j
        rw [one_div, inv_pow, pow_succ']
        field_simp
      rw [hfun]
      simpa using hpow.const_mul Δtprev
    · exact Eventually.of_forall fun j => Set.mem_Ioi.mpr (by positivity)
  have hboth := (aux_eventually_particularSolutionError_le (toRealMat sys.A) tk
      U₀.isBounded_construct 2 htpos hεmax hζ1 hacc).and
    (aux_eventually_nonAccumulating_le (toRealMat sys.A) H ũ tk U₀.isBounded_construct 2
      htpos htend hεmax hacc)
  obtain ⟨j, ha, hn⟩ := (hseq.eventually hboth).exists
  -- at that candidate the coarsest order clears both shares, so the order sweep reports it
  have hord := aux_autoTuneOrder_exists sys le H ũ tk U₀ (2 * Δtprev / 2 ^ (j + 1)) _ _ hηmax
    (by rw [Bool.and_eq_true]; exact ⟨hle _ _ ha, hle _ _ hn⟩)
  obtain ⟨p, hp⟩ := aux_autoTuneSearch_exists sys le H ũ tk tend εmax ζ εaAcc ηmax U₀ j
    (2 * Δtprev) 2 hord
  refine ⟨j + 1, p.1, p.2, ?_, aux_autoTuneSearch_pos sys le H ũ tk tend εmax ζ εaAcc ηmax U₀
    (j + 1) (2 * Δtprev) p hΔt₀ hp⟩
  rw [LinearSys.autoTuneDeltaT]
  exact hp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
