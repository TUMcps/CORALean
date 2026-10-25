module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# Zonotopes: the representation

The matrix zonotope, `Zonotope (Mat ℝ m n)`, is [1, Eq. (8)]. CORA's `zonotope` [2, Def. 1], with
the same center `c` and generator matrix `G`, denotes every point the generators reach from `c`
with coefficients in `[-1, 1]`. Over any real module, not just `Vec ℝ n`: nothing about a center
plus a bounded combination of generators mentions coordinates, so `Zonotope (Mat ℝ n m)` is CORA's
`matZonotope` and needs no separate development. Generators are a family rather than a matrix, a
matrix being available only when the ambient type has coordinates; at `Vec ℝ n` the two differ by
transposition: `G j i` is coordinate `i` of generator `j`. The generator count is a field, not a
type index: operations grow it freely and `reduce` is what bounds it, where the algorithm asks.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties, 2011.
* [2] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". Hybrid Systems:
      Computation and Control, 2005.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ========================================  MAIN TYPE  ========================================= --

/-- A zonotope: center `c` and `h` generators `G`. -/
structure Zonotope (α : Type) where
  h : ℕ
  c : α
  G : Fin h → α

/-- The set a zonotope denotes: the center plus the generators weighted by coefficients in `[-1,
1]`. -/
def Zonotope.construct (Z : Zonotope α) : Set α :=
  {x | ∃ β : Fin Z.h → ℝ, (∀ j, |β j| ≤ 1) ∧ x = Z.c + ∑ j, β j • Z.G j}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
