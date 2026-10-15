module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# `OptEmpty`: what a representation denotes, or nothing at all

An operation whose result can be empty has no answer inside a representation
that denotes only nonempty sets: a zonotope always holds its centre, so no
`Zonotope → Zonotope → Zonotope` returns the Minkowski difference of `{0}` and
`[-1, 1]`, which is `∅`. Wrapping the result is what gives it one.

`Option S` in shape and deliberately not in meaning. An `Option` here says a
*candidate the caller supplied* failed its check, as `Zonotope.minkDiffRep`'s
does — a statement about the input. `OptEmpty.empty` is a statement about the
set: it denotes `∅`, and a wrapper keeps the two from being read as one.

A wrapper rather than a sum with `EmptySet`: `S` already fixes the ambient
type, where `EmptySet n` fixes it to `Vec ℝ n`, so this extends the matrix and
module ambient types too — every type `ContSet` is indexed by.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {S α : Type}


-- ========================================  MAIN TYPE  ========================================= --

/-- A representation extended by an explicit empty set, for an operation whose
result can be empty where `S` has no way to say so. -/
inductive OptEmpty (S : Type) where
  | empty
  | of (s : S)

/-- `∅` at `empty`, and what `S` denotes at everything else. -/
def OptEmpty.construct [ContSet S α] : OptEmpty S → Set α
  | .empty => ∅
  | .of s => ContSet.construct s

instance [ContSet S α] : ContSet (OptEmpty S) α := ⟨OptEmpty.construct⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
