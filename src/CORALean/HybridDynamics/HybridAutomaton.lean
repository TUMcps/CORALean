import CORALean.HybridDynamics.Location

/-!
# Hybrid automata: the automaton and its runs

CORA's `hybridAutomaton`: the locations, indexed by a type. Finiteness is never
used and so is not required — `Fin k` is the intended index and `L` may be
anything.

## How a run is written, and why

A run alternates: flow inside a location over `[0, τ]` staying in its invariant,
then a jump through an outgoing transition whose guard the endpoint meets,
landing at the reset image in the target location. Three ways to say that were
available, and the choice is what everything downstream inherits.

*An inductive family*, as `NeuralNetwork` is — chosen. A run is a nonempty chain
of stays joined by jumps, and `Run ℓ x ℓ' y` reads "from state `x` in location
`ℓ`, this automaton can reach `y` in location `ℓ'`". Its recursion principle is
the chaining argument: `Theorems.RunOuter` is an `induction` with one case per
constructor and nothing else in it, exactly as `NeuralNetwork.propagate_outer`
is. That is the whole reason for the choice — the alternatives make the same
statement provable, but not free.

*A list of segments with conditions relating consecutive ones* was the
alternative, and it costs an index arithmetic that buys nothing: every proof
would carry `i < segments.length` and the condition tying segment `i` to `i + 1`
would be looked up rather than destructed. It becomes the better shape only when
a run has to be *manipulated* — reversed, concatenated, truncated at a step
count — and nothing here does that.

*A predicate on a pair of functions* `(ℝ → L) × (ℝ → Vec ℝ n)` over global time
was rejected for a specific reason: it forces the jump times into the statement,
so it has to say that they are discrete and increasing, which is a Zeno
condition smuggled into the definition of a run. The inductive family has no
such obligation — a chain is finite because it is a chain — and Zeno behaviour
stays what it is, a property of a family of runs rather than a well-formedness
side condition on one.

`flow` is the base case rather than a `nil`: a run always ends inside a
location, never in mid-jump, and a jump has no meaning without the stay that
brought the state to the guard. `Run ℓ x ℓ x` is `flow` at `τ = 0`, which asks
that `x` satisfy the invariant — reflexivity, but not for free, and rightly so.
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
