import CORALean.ContDynamics.NonlinearSys.AbstractionError
import CORALean.ContDynamics.NonlinearSys.Operations.LinInput

/-!
# One step of the re-linearization loop

A single linearization is `AbstractionError` together with the matrices and the
expansion point it was issued for. Bundling them is what makes a *sequence* of
linearizations sayable at all: seven parallel families indexed by the step count
is not a statement anyone can read, and the certificate has to travel with the
data it certifies or the wrong `L` can be handed to the wrong `A`.

## How a chain of steps is carried, and why

The loop re-linearizes at every step, so the analysis is a family of these. Three
shapes were available.

*A function `ℕ → LinStep`* — chosen. `relinReach` recurses on the step index and
looks nothing up; the composition theorem is `Nat.rec` with one hypothesis
family `∀ i < N` per obligation, and a chain longer than the horizon costs
nothing, since the steps past `N` are simply never named.

*A list* was the obvious alternative and it buys nothing here. Every statement
and every proof step would carry `i < steps.length`, and the horizon would be
`steps.length` — pinning the number of steps to the data, when the honest
statement is about the first `N` steps of a chain that may run further. A list
wins where a chain is *manipulated* — concatenated, truncated, reversed — and
nothing here does that, which is the same reading `HybridAutomaton.Run`'s
docstring gives.

*An inductive chain in the manner of `HybridAutomaton.Run`* was the tempting one,
and it is wrong for a sharp reason: a hybrid run is a datum of the *system* —
the automaton produces it and the analysis must cover every one — whereas a
chain of linearizations is a datum of the *analysis*, chosen by the caller.
Making it inductive would put the enclosures inside the proof, existentially,
and reachability's whole product is a set the caller hands to `Specification`.
A set that exists only once a proof has been built is not a set anything can be
checked against. `relinReach` has to be a `def`, so the steps have to be data an
index can address.

## What a step does not carry

The time step `Δt` and the order bound `o` are uniform across the loop and stay
arguments of `relinReach`: varying them per step is adaptive tuning, which is a
separate method with its own error measures.

The discrete input set is not here either. It is what the step is *run* with
rather than what the linearization *is*, and it is exactly what the two
composition theorems differ in — assumed in one, named as `inputSolution` in the
other — so it stays a separate family, as `LinearSysDT.reach` keeps its input
set separate from its system.

`R` is a plain `Set`, as `AbstractionError`'s is: confinement is checked, never
computed here, so nothing asks it to be a representation.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [OfInterval S]

/-- One linearization of `sys`, with the certificate that makes it conservative
wherever the state stays in `R`. -/
structure NonlinearSys.LinStep (sys : NonlinearSys n m) (U : S m) where
  A : Mat ℝ n n
  B : Mat ℝ n m
  xs : Vec ℝ n
  us : Vec ℝ m
  R : Set (Vec ℝ n)
  L : S n
  cert : AbstractionError sys A B xs us R (construct U) L

/-- The input set this step's linear system has to be given. -/
def NonlinearSys.LinStep.linInput {sys : NonlinearSys n m} {U : S m}
    (step : sys.LinStep U) : S n :=
  sys.linInput step.A step.B step.xs step.us U step.L

end CORALean.Real
