module

public import CORALean.HybridDynamics.Operations.LocationStayFloat
public import CORALean.HybridDynamics.Theorems.LocationReachFloatOuterWindow

@[expose] public section

/-!
# `Location.stayFloat` holds every state of a stay, window by window

A state of a stay of length `τ ≤ N Δt` at time `t` lies in the window `k` with
`k Δt ≤ t ≤ (k + 1) Δt` of `Location.reachFloat`. The windows after the first one certified
disjoint from the invariant are dropped, and the stay is in the invariant throughout: if a window
`j` before `k` were disjoint from it, the state at time `(j + 1/2) Δt ≤ t` would be in window
`j` (and nowhere else) and in the invariant. So the window `k` is among the kept ones.

## Inputs
* `ℓ` – location
* `τ` – stay duration
* `x` – trajectory of the stay
* `u` – input trajectory
* `w` – disturbance trajectory
* `N` – number of steps
* `options` – reach options
* `X₀` – initial zonotope
* `t` – time within the stay

## Hypotheses
* `traj` – the curves are a stay of the location
* `hN` – at least one step
* `h₀` – initial state lies in the initial set
* `hτ` – stay duration within `N` steps
* `ht` – time within the stay

## Conclusion
* the window of the time holds the state, and its start is not after the time
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic ContSet ContSetLike

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A state of a stay of at most `N` steps, at the time `t`, is in a kept window that starts at or
before `t`. -/
theorem Location.IsTrajectory.stayFloat_outer_window
    {ℓ : Location 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n} {τ : ℝ} {x : ℝ → Vec ℝ n} {u w}
    (traj : ℓ.IsTrajectory τ x u w) {N : ℕ} (hN : 0 < N)
    {options : LinearSys.ReachFloatOptions 𝕋} {X₀ : Zonotope (Vec 𝕋 n)} (h₀ : x 0 ∈ toSet X₀)
    (hτ : τ ≤ N * toReal options.Δt) {t : ℝ} (ht : t ∈ Set.Icc 0 τ) : -- --- CONCL ---
    ∀ Rs ∈ ℓ.stayFloat N options X₀, ∃ k, ∃ hk : k < Rs.length,
      x t ∈ toSet Rs[k] ∧ (k : ℝ) * toReal options.Δt ≤ t := by -- --- PROOF ---
  intro Rs (h : ℓ.stayFloat N options X₀ = some Rs)
  unfold Location.stayFloat at h
  rw [if_neg hN.ne'] at h
  obtain ⟨Rs₀, hRs₀, h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  -- the horizon of `reachFloat` is `N Δt`
  have hτ' : τ ≤ ((N * ToRat.toRat options.Δt : ℚ) : ℝ) := by
    rw [Rat.cast_mul, Rat.cast_natCast, ToRat.toReal_toRat]
    exact hτ
  have hwin := fun (s : ℝ) (hs : s ∈ Set.Icc 0 τ) => traj.reachFloat_outer_window h₀ hτ' hs Rs₀ hRs₀
  obtain ⟨hΔ, k, hk, hx, hkt, -⟩ := hwin t ht
  -- no window before `k` is certified disjoint from the invariant
  have hnone : ∀ j (hj : j < k), IsDisjoint.isDisjoint ℓ.inv Rs₀[j] = false := by
    intro j hj
    by_contra hcon
    have hdis : IsDisjoint.isDisjoint ℓ.inv Rs₀[j] = true := by simpa using hcon
    -- the state half a step into window `j`
    set s : ℝ := ((j : ℝ) + 1 / 2) * toReal options.Δt with hs
    have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
    have hs0 : 0 ≤ s := by positivity
    have hsk : s ≤ (k : ℝ) * toReal options.Δt := by
      rw [hs]; exact mul_le_mul_of_nonneg_right (by linarith) hΔ.le
    have hsτ : s ∈ Set.Icc 0 τ := ⟨hs0, by linarith [ht.2]⟩
    obtain ⟨-, k', hk', hxs, hk't, hk'u⟩ := hwin s hsτ
    -- which is window `j` only
    have h1 : (k' : ℝ) ≤ (j : ℝ) + 1 / 2 := by
      by_contra hlt
      push Not at hlt
      have := mul_lt_mul_of_pos_right hlt hΔ
      linarith
    -- the end of that window is not before the half step
    have h2 : (j : ℝ) + 1 / 2 ≤ (k' : ℝ) + 1 := by
      by_contra hlt
      push Not at hlt
      have := mul_lt_mul_of_pos_right hlt hΔ
      linarith
    -- the window is `j`, a whole number
    have hk'j : k' = j := by
      have a : k' ≤ j := by
        by_contra hc
        push Not at hc
        have : (j : ℝ) + 1 ≤ k' := by exact_mod_cast hc
        linarith
      have b : j ≤ k' := by
        by_contra hc
        push Not at hc
        have : (k' : ℝ) + 1 ≤ j := by exact_mod_cast hc
        linarith
      omega
    -- so the state is in window `j`, which is disjoint from the invariant: a contradiction
    subst hk'j
    exact Set.disjoint_left.mp (IsDisjoint.isDisjoint_sound _ _ hdis) hxs
      (traj.invariant s hsτ)
  -- no window before `k` stops the prefix, so `k` is kept
  obtain ⟨hk'', he⟩ := getElem_takeThrough (fun R => IsDisjoint.isDisjoint ℓ.inv R) Rs₀ k hk hnone
  exact ⟨k, hk'', by rw [he]; exact hx, hkt⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
