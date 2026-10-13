import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.ContSet.Interval.Real.Operations.Point

/-!
# The input set a linearization widens to

Rearranging `f(x,u) = f(x✱,u✱) + A(x - x✱) + B(u - u✱) + L(x,u)` moves
everything but `A x` into the input:

`ẋ = A x + ũ(t)`, `ũ(t) = f(x✱,u✱) - A x✱ + B(u(t) - u✱) + L(x(t), u(t))`,

so the set every admissible `ũ(t)` lies in is
`{f(x✱,u✱) - A x✱} ⊞ B(U ⊖ u✱) ⊞ L`. That is the whole construction: two
points, one `mtimes` and three `plus`es. A translation is a `plus` with a box
of zero width, which is why `OfInterval` is asked for and no translation
operation is.

The result lives at the state dimension rather than the input one — `B` has
already carried `U` across — which is what lets `LinearSys`, whose input is
additive and so state-dimensional, take it unchanged.
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
