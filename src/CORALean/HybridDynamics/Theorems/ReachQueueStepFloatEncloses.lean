module

public import CORALean.HybridDynamics.Definitions.Encloses
public import CORALean.HybridDynamics.Operations.ReachQueueStepFloat
public import CORALean.HybridDynamics.Theorems.LocationStayFloatOuter
public import CORALean.HybridDynamics.Theorems.LocationQueueJumpFloatEncloses
public import CORALean.HybridDynamics.Theorems.LocationMemQueueSetsFloatOfJump
public import CORALean.HybridDynamics.Theorems.LocationPotIntComplete
public import CORALean.HybridDynamics.Theorems.GuardGroupsMem
public import CORALean.ContDynamics.Reach.Theorems.StepCountReal

@[expose] public section

/-!
# One pass of `HybridAutomaton.reachQueueFloat` encloses the runs from its entry

If the entries the pass adds to the queue are enclosed and the branch is among `out`, the entry is
enclosed. A run from the entry is a stay or a stay and a jump. The stay is held by a window of the
branch (`Location.IsTrajectory.stayFloat_outer_window`, `Reach.stepCount_real`). At a jump the state
is in a window `k` and the guard, so the pair is a hit (`Location.potInt_complete`) in a crossing
that starts at `j₀ ≤ k` (`Location.guardGroups_mem`); its entry holds the reset state
(`Location.queueJumpFloat_encloses`). With `checkFlow` the set of the state is kept because the
stay, of positive length, came from the invariant (`Location.mem_queueSetsFloat_of_jump`): the runs
are those with positive dwell time (`IsRunUntilDwell`).

## Inputs
* `HA` – hybrid automaton
* `B` – basis
* `options` – reach options
* `δ` – margin to the horizon
* `out` – branches
* `idx` – number of the branch
* `p` – queue entry

## Hypotheses
* `horth` – the basis is orthogonal
* `hΔ` – the steps are positive
* `hδ` – the margin is at least every step
* `hfin` – no transition leads to `finalLoc`

## Conclusion
* if the pass's branch is among `out` and its entries are enclosed, so is the entry
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic ContSet ContSetLike Matrix

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] [DecidableEq L]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A successful `mapM` in `Option` has an answer for every entry. -/
private theorem aux_mapM_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ a ∈ l, ∃ b ∈ l', f a = some b
  | [], _, _, a, ha => absurd ha (List.not_mem_nil)
  | a :: l, l', h, a', ha' => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs, hbs, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    rcases List.mem_cons.mp ha' with rfl | ha'
    · exact ⟨b, List.mem_cons_self, hb⟩
    · obtain ⟨c, hc, hfc⟩ := aux_mapM_some hbs a' ha'
      exact ⟨c, List.mem_cons_of_mem _ hc, hfc⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.reachQueueStepFloat_encloses
    (HA : HybridAutomaton 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n) {B : Mat 𝕋 n n}
    (horth : Scalar.toRealMat B * (Scalar.toRealMat B)ᵀ = 1) {options : HybridReachOptions L 𝕋}
    (hΔ : ∀ ℓ, 0 < toReal (options.Δt ℓ)) {δ : ℝ} (hδ : ∀ ℓ, toReal (options.Δt ℓ) ≤ δ)
    (hfin : ∀ ℓ, ∀ e ∈ (HA.loc ℓ).trans, e.target ≠ options.finalLoc)
    (out : List (HybridBranch L 𝕋 n)) (idx : ℕ) (p : HybridPending L 𝕋 n) : -- --- CONCL ---
    ∀ r ∈ HA.reachQueueStepFloat B options idx p, r.1 ∈ out →
      (∀ c ∈ r.2, HA.Encloses options.checkFlow options.tFinal δ out c) →
        HA.Encloses options.checkFlow options.tFinal δ out p := by -- --- PROOF ---
  rintro ⟨br, js⟩ (hstep : HA.reachQueueStepFloat B options idx p = some (br, js)) hbr hjs
  unfold HybridAutomaton.reachQueueStepFloat at hstep
  dsimp only at hstep
  obtain ⟨Rs, hRs, hstep⟩ := Option.bind_eq_some_iff.mp hstep
  obtain ⟨jumps, hjumps, hstep⟩ := Option.bind_eq_some_iff.mp hstep
  cases hstep
  intro T k ℓ' x y run hx s hs hT
  -- the stay's steps, and its window
  have hΔq : 0 < ToRat.toRat (options.Δt p.loc) := by
    have := hΔ p.loc
    rw [← ToRat.toReal_toRat] at this
    exact_mod_cast this
  have hΔr : ((ToRat.toRat (options.Δt p.loc) : ℚ) : ℝ) = toReal (options.Δt p.loc) :=
    ToRat.toReal_toRat _
  -- a run is a stay, or a stay and a jump
  cases run with
  | @flow T ℓ τ x u w traj hτ =>
    -- the stay ends a step before the horizon, so it has a step and is within the steps
    have h0 := traj.nonneg
    have hτ1 : τ + ((ToRat.toRat (options.Δt p.loc) : ℚ) : ℝ) ≤
        (options.tFinal : ℝ) - (p.tlo : ℝ) := by
      rw [hΔr]; linarith [hδ p.loc]
    obtain ⟨hN, hτN⟩ := Reach.stepCount_real hΔq h0 hτ1
    rw [hΔr] at hτN
    -- the end state is in the window of the stay's last time
    obtain ⟨k, hk, hxk, -⟩ := traj.stayFloat_outer_window hN hx hτN ⟨h0, le_rfl⟩ Rs hRs
    exact ⟨_, hbr, rfl, Rs[k], List.getElem_mem hk, hxk⟩
  | @jump T k ℓ ℓ' τ x u w y e traj hτ hdw hmem hguard rest =>
    -- the stay ends a step before the horizon, so it has a step and is within the steps
    have h0 := traj.nonneg
    have hτ1 : τ + ((ToRat.toRat (options.Δt p.loc) : ℚ) : ℝ) ≤
        (options.tFinal : ℝ) - (p.tlo : ℝ) := by
      rw [hΔr]; linarith [hδ p.loc]
    obtain ⟨hN, hτN⟩ := Reach.stepCount_real hΔq h0 hτ1
    rw [hΔr] at hτN
    -- the window of the jump time
    obtain ⟨k₁, hk₁, hxk, hkτ⟩ := traj.stayFloat_outer_window hN hx hτN ⟨h0, le_rfl⟩ Rs hRs
    -- the guard is the `g`-th, and the pair is a hit
    obtain ⟨g, hg, rfl⟩ := List.mem_iff_getElem.mp hmem
    have hhit := Location.potInt_complete (HA.loc p.loc) Rs options.finalLoc hg hk₁
      (hfin _ _ hmem) hguard hxk
    -- in a crossing that starts no later
    obtain ⟨j₀, js', hgrp, hj₀, hkmem⟩ := Location.guardGroups_mem _ hhit
    obtain ⟨o, ho, hfo⟩ := aux_mapM_some hjumps _ hgrp
    -- the set of the jump state is kept by `checkFlow`: the stay came from the invariant
    have hkept : ∀ nv γ, (HA.loc p.loc).trans[g].guard.hyperplane? = some (nv, γ) →
        Rs[k₁] ∈ (HA.loc p.loc).queueSetsFloat options.checkFlow nv γ (j₀ :: js') Rs :=
      fun nv γ hhp => (HA.loc p.loc).mem_queueSetsFloat_of_jump options.checkFlow nv γ Rs hkmem
        (List.getElem?_eq_getElem hk₁) traj hdw hxk
        (HPolytope.dotProduct_of_hyperplane _ hguard (nv, γ) hhp)
    obtain ⟨c, rfl, hcloc, hcmem, hctlo⟩ := Location.queueJumpFloat_encloses (HA.loc p.loc)
      options.checkFlow B horth _ idx p.tlo p.thi Rs (List.getElem?_eq_getElem hg) hkept hxk
      hguard _ (Option.mem_def.mpr hfo)
    have hc : c ∈ jumps.filterMap id := List.mem_filterMap.mpr ⟨some c, ho, rfl⟩
    -- the entry starts no later than the jump
    have hstart : (c.tlo : ℝ) ≤ s + τ := by
      rw [hctlo]
      push_cast
      rw [hΔr]
      have h1 : (j₀ : ℝ) ≤ k₁ := by exact_mod_cast hj₀
      have h2 : (j₀ : ℝ) * toReal (options.Δt p.loc) ≤ k₁ * toReal (options.Δt p.loc) :=
        mul_le_mul_of_nonneg_right h1 (hΔ _).le
      linarith
    exact hjs c hc (by rw [hcloc]; exact rest) hcmem (s + τ) hstart (by linarith)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
