module

public import CORALean.HybridDynamics.Definitions.Location
public import CORALean.HybridDynamics.Operations.Basic

@[expose] public section

/-!
# Hybrid automata: the automaton and its runs

CORA's `hybridAutomaton`, [1, Def. 1] and [2, Def. 1] without invariants: the locations, indexed by
a type (`Fin k` is the intended index). A run alternates: flow inside a location over `[0, τ]`
staying in its invariant, then a jump through a transition whose guard the endpoint meets, landing
at the reset image in the target location; the guard is read as `construct e.guard` and never
otherwise (#39). The flow is [1, Def. 1]'s `ẋ = A x + u`, `u ∈ U`, read as a Carathéodory run
(`Location.IsTrajectory`). `IsRun` is an inductive family, so its recursion principle is the
chaining argument: `Theorems.IsRunOuter` is an `induction` with one case per constructor, and
`flow` is the base case since a jump has no meaning without the stay that brought the state to it.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid
      Systems Using a Combination of Zonotopes and Polytopes". Nonlinear
      Analysis: Hybrid Systems, 4(2):233-249, 2010.
* [2] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A hybrid automaton: a location for each index of `L`. -/
structure HybridAutomaton (S G : ℕ → Type) (L : Type) (𝕋 : Type) (n : ℕ) where
  loc : L → Location S G L 𝕋 n

/-- The runs of an automaton from a location and state to a location and state: a flow within a
location, or a flow followed by a transition whose guard holds at its end and a run from the reset
state. -/
inductive HybridAutomaton.IsRun {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (G n) (Vec ℝ n)] {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}
    (HA : HybridAutomaton S G L 𝕋 n) :
    L → Vec ℝ n → L → Vec ℝ n → Prop where
  | flow {ℓ : L} {τ : ℝ} {x : ℝ → Vec ℝ n} {u w} (h : (HA.loc ℓ).IsTrajectory τ x u w) :
      HA.IsRun ℓ (x 0) ℓ (x τ)
  | jump {ℓ ℓ' : L} {τ : ℝ} {x : ℝ → Vec ℝ n} {u w} {y : Vec ℝ n} {e : Transition G L 𝕋 n}
      (h : (HA.loc ℓ).IsTrajectory τ x u w) (hmem : e ∈ (HA.loc ℓ).trans)
      (hguard : x τ ∈ construct e.guard)
      (rest : HA.IsRun e.target (e.reset (x τ)) ℓ' y) :
      HA.IsRun ℓ (x 0) ℓ' y

-- `IsRun` with the jump count carried alongside, exact rather than a bound.
/-- The runs of an automaton with their jump count: a flow takes none, a transition adds one. -/
inductive HybridAutomaton.IsRunOn {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (G n) (Vec ℝ n)] {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}
    (HA : HybridAutomaton S G L 𝕋 n) :
    ℕ → L → Vec ℝ n → L → Vec ℝ n → Prop where
  | flow {ℓ : L} {τ : ℝ} {x : ℝ → Vec ℝ n} {u w} (h : (HA.loc ℓ).IsTrajectory τ x u w) :
      HA.IsRunOn 0 ℓ (x 0) ℓ (x τ)
  | jump {k : ℕ} {ℓ ℓ' : L} {τ : ℝ} {x : ℝ → Vec ℝ n} {u w} {y : Vec ℝ n}
      {e : Transition G L 𝕋 n} (h : (HA.loc ℓ).IsTrajectory τ x u w)
      (hmem : e ∈ (HA.loc ℓ).trans) (hguard : x τ ∈ construct e.guard)
      (rest : HA.IsRunOn k e.target (e.reset (x τ)) ℓ' y) :
      HA.IsRunOn (k + 1) ℓ (x 0) ℓ' y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
