module

public import CORALean.HybridDynamics.Definitions.IsUrgentRun

@[expose] public section

/-!
# The reachable set at a point in time

[1, Def. 2]: `R^e_{vᵢ}(r)`, the continuous states `x(r)` of the trajectories of [1, Def. 1]'s
automaton that start at `v₀` in `X₀` and are in location `vᵢ` at time `r`. `IsUrgentRunAt` is
`IsUrgentRun` with the time it lasts: the stays' dwell times add up to `r`, and the jumps take no
time. A state in the middle of a stay is the end of a shorter run, a stay cut short being a
stay. `HybridAutomaton.reachSetExact` reads the same runs at every time at once; the theorem
`urgentReachSetAtExact_subset_reachSetExact` puts this set inside it.

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


-- ========================================  MAIN TYPE  ========================================= --

/-- An urgent run from `x` at `ℓ` to `y` at `ℓ'` lasting `r` in all. -/
inductive HybridAutomaton.IsUrgentRunAt {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (G n) (Vec ℝ n)] {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}
    (HA : HybridAutomaton S G L 𝕋 n) :
    ℝ → L → Vec ℝ n → L → Vec ℝ n → Prop where
  | flow {ℓ : L} {τ : ℝ} {x : ℝ → Vec ℝ n} {u w} (h : (HA.loc ℓ).IsTrajectory τ x u w)
      (hfree : (HA.loc ℓ).IsGuardFreeBefore τ x) :
      HA.IsUrgentRunAt τ ℓ (x 0) ℓ (x τ)
  | jump {r : ℝ} {ℓ ℓ' : L} {τ : ℝ} {x : ℝ → Vec ℝ n} {u w} {y : Vec ℝ n}
      {e : Transition G L 𝕋 n} (h : (HA.loc ℓ).IsTrajectory τ x u w)
      (hfree : (HA.loc ℓ).IsGuardFreeBefore τ x) (hmem : e ∈ (HA.loc ℓ).trans)
      (hguard : x τ ∈ construct e.guard)
      (rest : HA.IsUrgentRunAt r e.target (e.reset (x τ)) ℓ' y) :
      HA.IsUrgentRunAt (τ + r) ℓ (x 0) ℓ' y

/-- [1, Def. 2]: `R^e_{vᵢ}(r)`, every state some urgent run from `v₀` with an initial state in
`X₀` is at, in location `vᵢ`, at time `r`. -/
def HybridAutomaton.urgentReachSetAtExact (HA : HybridAutomaton S G L 𝕋 n) (X₀ : S n) (v₀ vᵢ : L)
    (r : ℝ) : Set (Vec ℝ n) :=
  {y | ∃ x, x ∈ construct X₀ ∧ HA.IsUrgentRunAt r v₀ x vᵢ y}

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
