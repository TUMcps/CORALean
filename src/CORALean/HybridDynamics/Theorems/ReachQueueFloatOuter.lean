module

public import CORALean.HybridDynamics.Theorems.ReachQueueLoopFloatEncloses

@[expose] public section

/-!
# `HybridAutomaton.reachQueueFloat` holds every run it was asked about

Every run from `X₀` at `ℓ₀` that starts at the time `tStart` and ends at least `δ` before the
horizon, `δ` at least the step of every location, ends in a time-interval set of a branch of its end
location. A run is a stay or a stay and a jump, and a pass of the queue encloses both
(`reachQueueLoopFloat_encloses`, from the entry `X₀`). The margin is the last whole step: a stay
is cut at `Reach.stepCount` steps. No transition may lead to `finalLoc`, whose entry the algorithm
does not follow. With `options.checkFlow` (CORA's filter, on by default) the runs are those whose
stays before a jump are positive, and only a guard whose invariant side a row of the invariant
certifies is filtered (`Location.guardOrientFloat?`); without it, every run.

## Inputs
* `HA` – hybrid automaton
* `B` – basis
* `options` – reach options
* `δ` – margin to the horizon
* `tStart` – start time
* `ℓ₀` – initial location
* `X₀` – initial zonotope
* `T` – duration
* `k` – number of jumps
* `ℓ'` – end location
* `x` – start state
* `y` – end state

## Hypotheses
* `horth` – the basis is orthogonal
* `hΔ` – the steps are positive
* `hδ` – the margin is at least every step
* `hfin` – no transition leads to `finalLoc`
* `run` – run of duration `T` with `k` jumps, every dwell time positive if `options.checkFlow`
* `hx` – start state lies in the initial zonotope
* `hT` – the run ends `δ` before the horizon

## Conclusion
* the end state lies in a time-interval set of a branch of the end location
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic ContSetLike Matrix

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] [DecidableEq L]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.reachQueueFloat_outer
    (HA : HybridAutomaton 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n) {B : Mat 𝕋 n n}
    (horth : Scalar.toRealMat B * (Scalar.toRealMat B)ᵀ = 1) {options : HybridReachOptions L 𝕋}
    (hΔ : ∀ ℓ, 0 < toReal (options.Δt ℓ)) {δ : ℝ} (hδ : ∀ ℓ, toReal (options.Δt ℓ) ≤ δ)
    (hfin : ∀ ℓ, ∀ e ∈ (HA.loc ℓ).trans, e.target ≠ options.finalLoc) (tStart : ℚ) (ℓ₀ : L)
    (X₀ : Zonotope (Vec 𝕋 n)) {T : ℝ} {k : ℕ} {ℓ' : L} {x y : Vec ℝ n}
    (run : HA.IsRunUntilDwell options.checkFlow T k ℓ₀ x ℓ' y) (hx : x ∈ toSet X₀)
    (hT : (tStart : ℝ) + T + δ ≤ options.tFinal) : -- --- CONCL ---
    ∀ out ∈ HA.reachQueueFloat B options tStart ℓ₀ X₀,
      ∃ b ∈ out, b.loc = ℓ' ∧ ∃ R ∈ b.sets, y ∈ toSet R := by -- --- PROOF ---
  intro out h
  obtain ⟨-, hcov⟩ := HA.reachQueueLoopFloat_encloses horth hΔ hδ hfin _ _ _ out h
  exact hcov _ (List.mem_singleton_self _) run hx tStart le_rfl hT

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
