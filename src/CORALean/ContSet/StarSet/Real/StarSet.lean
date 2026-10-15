module

public import CORALean.Global.Tensor
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Star sets: the representation

The star set `(c, G, C, d, l, u)` of CORA's `neuralNetwork`, which evaluates a `conZonotope` by
converting it, in `nnHelper.conversionConZonoStarSet`, to this tuple and propagating it: the points
`{c + G α | C α ≤ d, l ≤ α ≤ u}`, the vectors `l` and `u` bounding the factors `α`. The
constraints are kept as a list of rows `(a, b)`, `a · α ≤ b`, which is `C` and `d` read row by row,
so a layer that adds a factor and three constraints appends to the list. The bounds belong to the
denotation: CORA's conversion computes them from the constraints, so for a set it builds they are
implied and change nothing, and a bound a step relies on is then the bound the set already
satisfies.

This is the generalized star set of [1, Def. 1] (center, basis, predicate on the coefficients)
with a linear predicate. The set is then convex, in fact a bounded polytope: the conversions to
and from `ConZonotope` (`Conversion/`) are exact. A nonlinear predicate is not this class.

At `Vec ℝ n`, with the generators stored row-wise (`G i k` is the `i`-th coordinate of the
`k`-th generator), as the neural-network layers read them.

## References

* [1] P. S. Duggirala and M. Viswanathan. "Parsimonious, Simulation Based Verification of Linear
      Systems". CAV, 2016.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

structure StarSet (n : ℕ) where
  m : ℕ
  c : Vec ℝ n
  G : Fin n → Fin m → ℝ
  cons : List ((Fin m → ℝ) × ℝ)
  l : Fin m → ℝ
  u : Fin m → ℝ

/-- The points `c + G α` over the factors `α` in the box `[l, u]` with every row satisfied. -/
def StarSet.construct {n : ℕ} (s : StarSet n) : Set (Vec ℝ n) :=
  {x | ∃ α : Fin s.m → ℝ, (∀ k, s.l k ≤ α k ∧ α k ≤ s.u k) ∧
    (∀ r ∈ s.cons, ∑ k, r.1 k * α k ≤ r.2) ∧ ∀ i, x i = s.c i + ∑ k, s.G i k * α k}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
