import CORALean.HybridDynamics.Location

/-!
# Hybrid automata: the automaton and its runs

CORA's `hybridAutomaton`: the locations, indexed by a type. Finiteness is never
used and so is not required; `Fin k` is the intended index.

A run alternates: flow inside a location over `[0, τ]` staying in its invariant,
then a jump through an outgoing transition whose guard the endpoint meets,
landing at the reset image in the target location.

`Run` is an inductive family, as `NeuralNetwork` is, so its recursion principle
*is* the chaining argument — `Theorems.RunOuter` is an `induction` with one case
per constructor. A predicate over global time would force the jump times into the
statement and so have to say they are discrete and increasing, a Zeno condition
smuggled into the definition of a run.

`flow` is the base case rather than a `nil`: a run always ends inside a location,
and a jump has no meaning without the stay that brought the state to the guard.
`Run ℓ x ℓ x` is `flow` at `τ = 0`, which asks that `x` satisfy the invariant.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet Scalar

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}

structure HybridAutomaton (S : ℕ → Type) (L : Type) (𝕋 : Type) (n : ℕ) where
  loc : L → Location S L 𝕋 n

inductive HybridAutomaton.Run {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
    {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ} (HA : HybridAutomaton S L 𝕋 n) :
    L → Vec ℝ n → L → Vec ℝ n → Prop where
  | flow {ℓ : L} {τ : ℝ} {x u : ℝ → Vec ℝ n} (h : (HA.loc ℓ).Trajectory τ x u) :
      HA.Run ℓ (x 0) ℓ (x τ)
  | jump {ℓ ℓ' : L} {τ : ℝ} {x u : ℝ → Vec ℝ n} {y : Vec ℝ n} {e : Transition S L n}
      (h : (HA.loc ℓ).Trajectory τ x u) (hmem : e ∈ (HA.loc ℓ).trans)
      (hguard : x τ ∈ construct e.guard)
      (rest : HA.Run e.target (e.reset (x τ)) ℓ' y) :
      HA.Run ℓ (x 0) ℓ' y

end CORALean.Real
