module

public import CORALean.HybridDynamics.Definitions.UrgentRun

@[expose] public section

/-!
# The reachable set at a point in time

[1, Def. 2]: `R^e_{vᵢ}(r)`, the continuous states `x(r)` of the trajectories of [1, Def. 1]'s
automaton that start at `v₀` in `X₀` and are in location `vᵢ` at time `r`. `UrgentRunAt` is
`UrgentRun` with the time it lasts: the stays' dwell times add up to `r`, and the jumps take no
time. A state in the middle of a stay is the end of a shorter run, a stay cut short being a
stay. `HybridAutomaton.reachSet` reads the same runs at every time at once; the theorem
`urgentReachSetAt_subset_reachSet` puts this set inside it.

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


-- ========================================  MAIN TYPE  ========================================= --

/-- An urgent run from `x` at `ℓ` to `y` at `ℓ'` lasting `r` in all. -/
inductive HybridAutomaton.UrgentRunAt {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (G n) (Vec ℝ n)] {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}
    (HA : HybridAutomaton S G L 𝕋 n) :
    ℝ → L → Vec ℝ n → L → Vec ℝ n → Prop where
  | flow {ℓ : L} {τ : ℝ} {x : ℝ → Vec ℝ n} {u w} (h : (HA.loc ℓ).Trajectory τ x u w)
      (hfree : (HA.loc ℓ).GuardFreeBefore τ x) :
      HA.UrgentRunAt τ ℓ (x 0) ℓ (x τ)
  | jump {r : ℝ} {ℓ ℓ' : L} {τ : ℝ} {x : ℝ → Vec ℝ n} {u w} {y : Vec ℝ n}
      {e : Transition G L 𝕋 n} (h : (HA.loc ℓ).Trajectory τ x u w)
      (hfree : (HA.loc ℓ).GuardFreeBefore τ x) (hmem : e ∈ (HA.loc ℓ).trans)
      (hguard : x τ ∈ construct e.guard)
      (rest : HA.UrgentRunAt r e.target (e.reset (x τ)) ℓ' y) :
      HA.UrgentRunAt (τ + r) ℓ (x 0) ℓ' y

/-- [1, Def. 2]: `R^e_{vᵢ}(r)`, every state some urgent run from `v₀` with an initial state in
`X₀` is at, in location `vᵢ`, at time `r`. -/
def HybridAutomaton.urgentReachSetAt (HA : HybridAutomaton S G L 𝕋 n) (X₀ : S n) (v₀ vᵢ : L)
    (r : ℝ) : Set (Vec ℝ n) :=
  {y | ∃ x, x ∈ construct X₀ ∧ HA.UrgentRunAt r v₀ x vᵢ y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
