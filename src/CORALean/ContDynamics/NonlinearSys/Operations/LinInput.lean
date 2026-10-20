module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.Conversion.Real.Instances
public import CORALean.ContSet.Interval.Real.Operations.Point

@[expose] public section

/-!
# The input set a linearization widens to

Rearranging `f(x,u) = f(x✱,u✱) + A(x - x✱) + B(u - u✱) + L(x,u)` moves everything but `A x`
into the input: `ẋ = A x + ũ(t)` with `ũ(t) = f(x✱,u✱) - A x✱ + B(u(t) - u✱) + L(x(t), u(t))`.
So the set every admissible `ũ(t)` lies in is `{f(x✱,u✱) - A x✱} ⊞ B(U ⊖ u✱) ⊞ L`: two points,
one `mtimes` and three `plus`es. A translation is a `plus` with a box of zero width. The result
lives at the state dimension, which lets `LinearSys` take it unchanged.

## Inputs
* `f` – field
* `A` – state Jacobian
* `B` – input Jacobian
* `xs` – state expansion point
* `us` – input expansion point
* `U` – input set
* `L` – remainder set

## Output
* the input set of the linearized system
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Plus Mtimes Real.OfInterval

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Real.OfInterval S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every input the linearized system needs in order to reproduce a run of `f`
that stays where the certificate holds. -/
def linInput (f : Vec ℝ n → Vec ℝ m → Vec ℝ n) (A : Mat ℝ n n) (B : Mat ℝ n m)
    (xs : Vec ℝ n) (us : Vec ℝ m) (U : S m) (L : S n) : S n :=
  ofInterval (Real.Interval.point (f xs us - A *ᵥ xs))
    ⊞ mtimes B (U ⊞ ofInterval (Real.Interval.point (-us)))
    ⊞ L

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
