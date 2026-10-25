module

public import CORALean.Global.MemOfReachSubset
public import CORALean.Global.RegionOfAttraction
public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

/-!
# The region-of-attraction criterion, where the limits exist

[1, Sec. 3.1.2]: "To verify the region of attraction, we have to show that for `R(0) = D`, it
holds that `∃ t > 0 : R(t) ⊆ S`." With `S` robust positively invariant (`IsRobustInvariant`)
and closed, the criterion puts `R(0)` inside the region of attraction `D`
(`regionOfAttraction`) once every solution from `R(0)` converges: from `t` on every solution
is in `S` (`IsRobustInvariant.mem_of_reach_subset`), so its limit is in the closed `S`. The
convergence is a hypothesis, and has to be: the criterion holds for a rotation, whose
solutions have no limit (`regionOfAttraction_counterexample`). `hγ` and `hU` are the
time-invariance and unique solutions of [1, Sec. 3.1].

## Inputs
* `γ` – solution map of the system
* `U` – set of admissible input signals
* `S` – robust invariant closed set
* `R₀` – set of initial states
* `t` – time

## Hypotheses
* `hS` – the set is robust positively invariant
* `hSc` – the set is closed
* `hγ` – the flow is time-invariant
* `hU` – shifted inputs are admissible
* `ht` – the time is positive
* `hR` – states from the initial set are in the set at the time
* `hconv` – every solution from the initial set converges

## Conclusion
* the initial set lies in the region of attraction

## References

* [1] M. Althoff. "Benchmarks for the Formal Verification of Power Systems". Proceedings of 9th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH22),
      2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Filter Topology

variable {X Inp : Type} [TopologicalSpace X]


-- =======================================  MAIN THEOREM  ======================================= --

theorem subset_regionOfAttraction_of_reach_subset {γ : ℝ → X → (ℝ → Inp) → X}
    {U : Set (ℝ → Inp)} {S R₀ : Set X} {t : ℝ} (hS : IsRobustInvariant γ U S) (hSc : IsClosed S)
    (hγ : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → ∀ x u, γ (t + s) x u = γ s (γ t x u) (fun r => u (t + r)))
    (hU : ∀ u ∈ U, ∀ t : ℝ, 0 ≤ t → (fun r => u (t + r)) ∈ U) (ht : 0 < t)
    (hR : ∀ x₀ ∈ R₀, ∀ u ∈ U, γ t x₀ u ∈ S)
    (hconv : ∀ x₀ ∈ R₀, ∀ u ∈ U, ∃ L, Tendsto (fun t => γ t x₀ u) atTop (𝓝 L)) : -- --- CONCL ---
    R₀ ⊆ regionOfAttraction γ U S := by -- --- PROOF ---
  intro x₀ hx₀ u hu
  obtain ⟨L, hL⟩ := hconv x₀ hx₀ u hu
  refine ⟨L, hSc.mem_of_tendsto hL ?_, hL⟩
  -- in `S` from `t` on
  filter_upwards [eventually_ge_atTop t] with t' ht'
  exact hS.mem_of_reach_subset hγ hU ht.le hR x₀ hx₀ u hu t' ht'

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
