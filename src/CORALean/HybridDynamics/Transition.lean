import CORALean.ContSet.ContSet.ContSet

/-!
# Hybrid automata: a transition

CORA's `transition`: the guard a run must meet to take it, the reset applied on
the way through, and the location it lands in.

The reset is affine, `x ↦ W x + w`, and stored as its coefficients rather than
as a function. That is not generality withheld for its own sake: `Mtimes` and
`Plus` are what an arbitrary representation propagates, so an enclosure of the
reset image is two existing operations and nothing new, whereas a general reset
would have to carry an enclosure of its own — `Layer`'s bargain, and not one to
make before something asks for it.

Over ℝ rather than over a layer's scalar, as `Layer.linear` is: the reset acts
on the exact state, and a float layer would store it rounded and pay the
difference into the enclosure rather than into this type.

`target` is an index into the automaton's locations, not a `Location`. A
location holds its outgoing transitions, so a transition holding its target
outright would make the two types mutually recursive for no gain.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {S : ℕ → Type} {L : Type} {n : ℕ}

structure Transition (S : ℕ → Type) (L : Type) (n : ℕ) where
  guard : S n
  W : Mat ℝ n n
  w : Vec ℝ n
  target : L

/-- The map the coefficients denote, which is what a run applies at a jump. -/
def Transition.reset (e : Transition S L n) (x : Vec ℝ n) : Vec ℝ n := e.W *ᵥ x + e.w

end CORALean.Real
