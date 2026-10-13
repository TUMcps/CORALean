module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# Capsules: the representation

CORA's `capsule`: a segment thickened by a Euclidean ball, `{c + t g | t ∈
[-1, 1]} ⊕ ball(0, r)`.

At `Vec ℝ n`, not over a general module: the ball is Euclidean and needs
coordinates. The distance is written out as `Real.sqrt (∑ …)` rather than
reached for as a norm, because `Vec ℝ n` is `Fin n → ℝ`, whose ambient norm
instance is the *supremum* norm, and `EuclideanSpace ℝ (Fin n)` is a type
synonym that would fight the `ContSet` instance already at `Vec ℝ n`. Spelling
the distance out costs two lemmas in the theorems below and avoids all of that.

A negative `r` denotes `∅`, since `Real.sqrt` is never negative — the same
convention `Interval` uses for a crossed box, and the reason the structure
below carries no `0 ≤ r` field.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Capsule (n : ℕ) where
  c : Vec ℝ n
  g : Vec ℝ n
  r : ℝ

/-- `r < 0` denotes `∅`: `Real.sqrt` never returns a negative value, so no `x`
can satisfy the bound. -/
def Capsule.construct (C : Capsule n) : Set (Vec ℝ n) :=
  {x | ∃ t ∈ Set.Icc (-1 : ℝ) 1,
        Real.sqrt (∑ i, (x i - (C.c i + t * C.g i)) ^ 2) ≤ C.r}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
