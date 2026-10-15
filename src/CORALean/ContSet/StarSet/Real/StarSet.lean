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

The predicate on the factors is linear, so the set is convex, and in fact a bounded polytope: the
conversions to and from `ConZonotope` (`Conversion/`) are exact, and a star set whose predicate
may be nonlinear, as the notion is used elsewhere, is not this class.

At `Vec ℝ n`, with the generators stored row-wise (`G i k` is the `i`-th coordinate of the
`k`-th generator), as the neural-network layers read them.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
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
