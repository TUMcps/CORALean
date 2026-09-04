import CORALean.ContSet.Conversion.Real.Interval_to_ContSet
import CORALean.ContSet.Interval.Real.Operations.Point
import CORALean.HybridDynamics.Transition

/-!
# `Transition.jump`

The reset propagated over a set: `mtimes` for the matrix, `plus` for the offset,
which is `Layer.linear` at a square matrix and for the same reason — a
representation closed under both loses nothing here.

The argument is the set *already cut down by the guard*, not the set entering
the location. Guard intersection is left outside on purpose: there is no `And`
class, deliberately, because only two representations implement one, so a `jump`
that intersected would either name a representation or invent an interface. What
it takes instead is whatever the caller could prove encloses the intersection —
`Theorems.JumpOuter` states that as its one hypothesis, and
`Theorems.JumpOuterConZonotope` discharges it exactly.

The offset enters as a box of zero width through `OfInterval`, as a bias does, so
no translation operation is needed. That is also what keeps `ConPolyZono` out: it
has `plus` and `mtimes` but no `OfInterval` instance, so its exact guard
intersection is one conversion instance away from running this.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Plus Mtimes OfInterval

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] {L : Type} {n : ℕ}

def Transition.jump (e : Transition S L n) (Rg : S n) : S n :=
  plus (mtimes e.W Rg) (ofInterval (Interval.point e.w))

end CORALean.Real
