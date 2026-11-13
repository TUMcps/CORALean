module

public import CORALean.HybridDynamics.Operations.ReachQueueFloat
public import CORALean.HybridDynamics.Theorems.ReachQueueStepFloatEncloses

@[expose] public section

/-!
# The loop of `HybridAutomaton.reachQueueFloat` encloses every entry it takes

By induction on the fuel: the branches only grow, and when the loop returns, every entry of the
queue is covered by the final branches. The first entry's pass is covered once the entries it
adds, which are at the end of the queue for the next call, and its own branch are
(`reachQueueStepFloat_encloses`).

## Inputs
* `HA` – hybrid automaton
* `Bf` – the basis of a crossing, from the guard normal and offset and the sets that meet the guard
* `options` – reach options
* `δ` – margin to the horizon
* `f` – fuel
* `q` – queue
* `acc` – branches so far

## Hypotheses
* `hΔ` – the steps are positive
* `hδ` – the margin is at least every step
* `hfin` – no transition leads to `finalLoc`

## Conclusion
* a result of the loop extends `acc` and encloses every entry of the queue
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix

variable {n : ℕ} {L 𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] [DecidableEq L]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HybridAutomaton.reachQueueLoopFloat_encloses
    (HA : HybridAutomaton 𝒵[𝕋] (fun k => HPolytope 𝕋 (Vec 𝕋 k)) L 𝕋 n) {Bf : BasisRule 𝕋 n}
    {options : HybridReachOptions L 𝕋}
    (hΔ : ∀ ℓ, 0 < toReal (options.Δt ℓ)) {δ : ℝ} (hδ : ∀ ℓ, toReal (options.Δt ℓ) ≤ δ)
    (hfin : ∀ ℓ, ∀ e ∈ (HA.loc ℓ).trans, e.target ≠ options.finalLoc) (f : ℕ)
    (q : List (HybridPending L 𝕋 n)) (acc : List (HybridBranch L 𝕋 n)) : -- --- CONCL ---
    ∀ out ∈ HA.reachQueueLoopFloat Bf options f q acc,
      (∃ rest, out = acc ++ rest) ∧
        ∀ p ∈ q, HA.Encloses options.checkFlow options.tFinal δ out p := by -- --- PROOF ---
  induction f generalizing q acc with
  | zero => intro out h; simp [HybridAutomaton.reachQueueLoopFloat] at h
  | succ f ih =>
    intro out (h : HA.reachQueueLoopFloat Bf options (f + 1) q acc = some out)
    -- the empty queue returns the branches, a first entry is analysed and its jumps queued
    cases q with
    | nil =>
      simp only [HybridAutomaton.reachQueueLoopFloat, Option.some.injEq] at h
      subst h
      exact ⟨⟨[], by simp⟩, by simp⟩
    | cons p q =>
      unfold HybridAutomaton.reachQueueLoopFloat at h
      obtain ⟨⟨br, js⟩, hstep, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨rest, hout⟩, hcov⟩ := ih _ _ out h
      refine ⟨⟨br :: rest, by simpa using hout⟩, ?_⟩
      intro p' hp'
      rcases List.mem_cons.mp hp' with rfl | hq
      · refine HA.reachQueueStepFloat_encloses hΔ hδ hfin out acc.length _ _ hstep
          (by simp [hout]) ?_
        exact fun c hc => hcov c (List.mem_append_right _ hc)
      · exact hcov p' (List.mem_append_left _ hq)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
