module

public import CORALean.HybridDynamics.Definitions.ReachSetExact
public import CORALean.HybridDynamics.Definitions.UrgentReachSetAtExact
public import CORALean.HybridDynamics.Theorems.IsUrgentRunToIsRun

@[expose] public section

/-!
# The reachable set at a time lies in the reachable set

[1, Def. 2]'s `R^e_{vᵢ}(r)` is inside `HybridAutomaton.reachSetExact`, which collects the states of
every run at every time: forgetting the time an urgent run lasts leaves an urgent run, and an
urgent run is a run. So every enclosure proved of `reachSetExact` encloses `R^e_{vᵢ}(r)` at each
`r`.

## Inputs
* `HA` – hybrid automaton
* `X₀` – initial set
* `v₀` – initial location
* `vᵢ` – end location
* `r` – time

## Hypotheses
* none

## Conclusion
* the urgent reach set at the time lies in the reachable set

## References

* [1] [M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control,
      2012.](../../../../references/2012/althoff-hscc-avoiding-intersection.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- An urgent run of a given duration is an urgent run. -/
private theorem aux_urgentRunAt_toUrgentRun {HA : HybridAutomaton S G L 𝕋 n} {r : ℝ} {ℓ ℓ' : L}
    {x y : Vec ℝ n} (h : HA.IsUrgentRunAt r ℓ x ℓ' y) : HA.IsUrgentRun ℓ x ℓ' y := by
  induction h with
  | flow h hfree => exact .flow h hfree
  | jump h hfree hmem hguard _ ih => exact .jump h hfree hmem hguard ih


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Def. 2]: `R^e_{vᵢ}(r) ⊆ reachSetExact X₀ v₀ vᵢ` at every time `r`. -/
theorem HybridAutomaton.urgentReachSetAtExact_subset_reachSetExact (HA : HybridAutomaton S G L 𝕋 n)
    (X₀ : S n) (v₀ vᵢ : L) (r : ℝ) :
    HA.urgentReachSetAtExact X₀ v₀ vᵢ r ⊆ HA.reachSetExact X₀ v₀ vᵢ := by
  rintro y ⟨x, hx, hrun⟩
  exact ⟨x, hx, (aux_urgentRunAt_toUrgentRun hrun).toIsRun⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
