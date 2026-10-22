module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Hybrid automata: a transition

CORA's `transition`: the guard a run must meet to take it, the reset applied on the way through,
and the location it lands in. `G` is the guard's own representation, not the reachable set's;
nothing here reads a guard, so `Transition` asks no class of `G` at all (#39). The reset is affine,
`x ↦ W x + w`, stored as coefficients rather than as a function, so an enclosure of the reset image
is two existing operations, `Mtimes` and `Plus`; `W` and `w` are read through `Scalar 𝕋`. `target`
is an index into the automaton's locations, not a `Location`: a location holds its outgoing
transitions, and holding the target outright would make the types mutually recursive.
-/

-- Authors:       Claude Sonnet 5
-- Written:       02-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {G : ℕ → Type} {L : Type} {𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A transition: the guard that must hold to take it, the affine reset `x ↦ W x + w`, and the
target location. -/
structure Transition (G : ℕ → Type) (L : Type) (𝕋 : Type) (n : ℕ) where
  guard : G n
  W : Mat 𝕋 n n
  w : Vec 𝕋 n
  target : L

/-- The map the coefficients denote, which is what a run applies at a jump. -/
noncomputable def Transition.reset (e : Transition G L 𝕋 n) (x : Vec ℝ n) : Vec ℝ n :=
  toRealMat e.W *ᵥ x + toRealVec e.w

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
