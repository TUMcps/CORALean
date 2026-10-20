module

public import CORALean.Global.RobustInvariant

@[expose] public section

/-!
# Once in an invariant set, always in it

What the verification of a region of attraction in [1, Sec. 3.1.2] shows: if `S` is robust
positively invariant (`RobustInvariant`) and the reachable set from `R(0)` lies in `S` at one
time, `∃ t > 0 : R(t) ⊆ S`, then every solution from `R(0)` is in `S` at every later time. That
the solution converges, which the region of attraction `D` asks for, it does not show
(`regionOfAttraction_counterexample`). The argument restarts the solution at `t`: the system of
[1, Eq. 4] is time-invariant with a unique solution [1, Sec. 3.1], so
`γ(t + s, x₀, u) = γ(s, γ(t, x₀, u), u(t + ·))` (`hγ`), and the shifted input is admissible (`hU`),
as for the input sets of [1, Sec. 3.3]. `R(t) ⊆ S` is stated pointwise.

## Inputs
* `γ` – flow of the system
* `U` – set of admissible inputs
* `S` – robust invariant set
* `R₀` – set of initial states
* `t` – time

## Hypotheses
* `hS` – the set is robust positively invariant
* `hγ` – the flow is time-invariant
* `hU` – shifted inputs are admissible
* `ht` – the time is nonnegative
* `hR` – states from the initial set are in the set at the time

## Conclusion
* every solution from the initial set stays in the set from the time on

## References

* [1] M. Althoff. "Benchmarks for the Formal Verification of Power Systems". In Proc. of the
      9th International Workshop on Applied Verification of Continuous and Hybrid Systems
      (ARCH22), EPiC Series in Computing, vol. 90, pp. 26-43, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {X Inp : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem RobustInvariant.mem_of_reach_subset {γ : ℝ → X → (ℝ → Inp) → X} {U : Set (ℝ → Inp)}
    {S R₀ : Set X} {t : ℝ} (hS : RobustInvariant γ U S)
    (hγ : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → ∀ x u, γ (t + s) x u = γ s (γ t x u) (fun r => u (t + r)))
    (hU : ∀ u ∈ U, ∀ t : ℝ, 0 ≤ t → (fun r => u (t + r)) ∈ U) (ht : 0 ≤ t)
    (hR : ∀ x₀ ∈ R₀, ∀ u ∈ U, γ t x₀ u ∈ S) : -- --- CONCL ---
    ∀ x₀ ∈ R₀, ∀ u ∈ U, ∀ t' ≥ t, γ t' x₀ u ∈ S := by -- --- PROOF ---
  intro x₀ hx₀ u hu t' ht'
  rcases eq_or_lt_of_le ht' with h | h
  · rw [← h]; exact hR x₀ hx₀ u hu
  -- restart at `t`, inside `S`, and run for `t' - t > 0`
  have hs : 0 < t' - t := sub_pos.mpr h
  have := hγ t (t' - t) ht hs.le x₀ u
  rw [add_sub_cancel] at this
  rw [this]
  exact hS _ hs _ (hU u hu t ht) _ (hR x₀ hx₀ u hu)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
