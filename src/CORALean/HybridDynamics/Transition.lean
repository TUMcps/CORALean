import CORALean.ContSet.ContSet.ContSet

/-!
# Hybrid automata: a transition

CORA's `transition`: the guard a run must meet to take it, the reset applied on
the way through, and the location it lands in.

The reset is affine, `x ↦ W x + w`, and stored as its coefficients rather than as
a function: `Mtimes` and `Plus` are what an arbitrary representation propagates,
so an enclosure of the reset image is two existing operations, where a general
reset would have to carry an enclosure of its own — `Layer`'s bargain.

`W` and `w` are read through `Scalar 𝕋`, as `LinearSysDT.A` is: `𝕋` says what
the coefficients are stored as, and `reset` acts on the real matrix and vector
they denote either way. A different axis from `Layer.linear`'s `FloatOps 𝕋`,
which rounds; nothing here rounds, at any `𝕋`.

`target` is an index into the automaton's locations, not a `Location`. A
location holds its outgoing transitions, so a transition holding its target
outright would make the two types mutually recursive for no gain.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix Scalar

variable {S : ℕ → Type} {L : Type} {𝕋 : Type} [Scalar 𝕋] {n : ℕ}

structure Transition (S : ℕ → Type) (L : Type) (𝕋 : Type) (n : ℕ) where
  guard : S n
  W : Mat 𝕋 n n
  w : Vec 𝕋 n
  target : L

/-- The map the coefficients denote, which is what a run applies at a jump. -/
def Transition.reset (e : Transition S L 𝕋 n) (x : Vec ℝ n) : Vec ℝ n :=
  toRealMat e.W *ᵥ x + toRealVec e.w

end CORALean.Real
