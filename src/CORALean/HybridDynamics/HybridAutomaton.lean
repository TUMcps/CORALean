import CORALean.HybridDynamics.Definitions.Location

/-!
# Hybrid automata: the automaton and its runs

CORA's `hybridAutomaton`, and [1, Def. 3.3]: the locations, indexed by a type. Finiteness is never
used and so is not required; `Fin k` is the intended index.

A run alternates: flow inside a location over `[0, τ]` staying in its invariant,
then a jump through a transition whose guard the endpoint meets, landing at the
reset image in the target location — the guard read as `construct e.guard` and
never otherwise, so the guard representation `G` enters with `ContSet` (#39).

`Run` is an inductive family, as `NeuralNetwork` is, so its recursion principle
*is* the chaining argument: `Theorems.RunOuter` is an `induction` with one case
per constructor. `flow` is the base case rather than a `nil`, since a jump has
no meaning without the stay that brought the state to the guard.

`RunOn` is `Run` with an exact jump count, not a bound: `RunOn k` for some
`k ≤ K` is how a caller states a bound, so the constructors carry no inequality.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure HybridAutomaton (S G : ℕ → Type) (L : Type) (𝕋 : Type) (n : ℕ) where
  loc : L → Location S G L 𝕋 n

inductive HybridAutomaton.Run {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (G n) (Vec ℝ n)] {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}
    (HA : HybridAutomaton S G L 𝕋 n) :
    L → Vec ℝ n → L → Vec ℝ n → Prop where
  | flow {ℓ : L} {τ : ℝ} {x u : ℝ → Vec ℝ n} (h : (HA.loc ℓ).Trajectory τ x u) :
      HA.Run ℓ (x 0) ℓ (x τ)
  | jump {ℓ ℓ' : L} {τ : ℝ} {x u : ℝ → Vec ℝ n} {y : Vec ℝ n} {e : Transition G L 𝕋 n}
      (h : (HA.loc ℓ).Trajectory τ x u) (hmem : e ∈ (HA.loc ℓ).trans)
      (hguard : x τ ∈ construct e.guard)
      (rest : HA.Run e.target (e.reset (x τ)) ℓ' y) :
      HA.Run ℓ (x 0) ℓ' y

-- `Run` with the jump count carried alongside, exact rather than a bound.
inductive HybridAutomaton.RunOn {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
    [∀ n, ContSet (G n) (Vec ℝ n)] {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}
    (HA : HybridAutomaton S G L 𝕋 n) :
    ℕ → L → Vec ℝ n → L → Vec ℝ n → Prop where
  | flow {ℓ : L} {τ : ℝ} {x u : ℝ → Vec ℝ n} (h : (HA.loc ℓ).Trajectory τ x u) :
      HA.RunOn 0 ℓ (x 0) ℓ (x τ)
  | jump {k : ℕ} {ℓ ℓ' : L} {τ : ℝ} {x u : ℝ → Vec ℝ n} {y : Vec ℝ n}
      {e : Transition G L 𝕋 n} (h : (HA.loc ℓ).Trajectory τ x u)
      (hmem : e ∈ (HA.loc ℓ).trans) (hguard : x τ ∈ construct e.guard)
      (rest : HA.RunOn k e.target (e.reset (x τ)) ℓ' y) :
      HA.RunOn (k + 1) ℓ (x 0) ℓ' y

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
