module

public import CORALean.HybridDynamics.Definitions.ReachSet
public import CORALean.HybridDynamics.Definitions.UrgentReachSetAt
public import CORALean.HybridDynamics.Theorems.UrgentRunToRun

@[expose] public section

/-!
# The reachable set at a time lies in the reachable set

[1, Def. 2]'s `R^e_{vᵢ}(r)` is inside `HybridAutomaton.reachSet`, which collects the states of
every run at every time: forgetting the time an urgent run lasts leaves an urgent run, and an
urgent run is a run. So every enclosure proved of `reachSet` encloses `R^e_{vᵢ}(r)` at each `r`.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
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
theorem aux_urgentRunAt_toUrgentRun {HA : HybridAutomaton S G L 𝕋 n} {r : ℝ} {ℓ ℓ' : L}
    {x y : Vec ℝ n} (h : HA.UrgentRunAt r ℓ x ℓ' y) : HA.UrgentRun ℓ x ℓ' y := by
  induction h with
  | flow h hfree => exact .flow h hfree
  | jump h hfree hmem hguard _ ih => exact .jump h hfree hmem hguard ih


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Def. 2]: `R^e_{vᵢ}(r) ⊆ reachSet X₀ v₀ vᵢ` at every time `r`. -/
theorem HybridAutomaton.urgentReachSetAt_subset_reachSet (HA : HybridAutomaton S G L 𝕋 n)
    (X₀ : S n) (v₀ vᵢ : L) (r : ℝ) :
    HA.urgentReachSetAt X₀ v₀ vᵢ r ⊆ HA.reachSet X₀ v₀ vᵢ := by
  rintro y ⟨x, hx, hrun⟩
  exact ⟨x, hx, (aux_urgentRunAt_toUrgentRun hrun).toRun⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
