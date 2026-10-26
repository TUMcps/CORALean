module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# Capsules: the representation

CORA's `capsule`: a segment thickened by a Euclidean ball, `{c + t g | t ∈ [-1, 1]} ⊕ ball(0, r)`
[1, Sec. 2.2.1.7].

At `Vec ℝ n`, not a general module: the ball is Euclidean. The distance is written out as
`Real.sqrt (∑ …)`, because the ambient norm of `Fin n → ℝ` is the supremum norm and `EuclideanSpace`
would fight the `ContSet` instance at `Vec ℝ n`. A negative `r` denotes `∅`, as `Interval` does for
a crossed box, which is why the structure has no `0 ≤ r` field.

## References

* [1] M. Althoff, N. Kochdumper, T. Ladner, M. Perschl and M. Wetzlinger. "CORA Manual (v2026)".
      Technische Universität München, 2026.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A capsule with center `c`, generator `g` and radius `r`: the points within `r` of the segment `c
± g`. -/
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
