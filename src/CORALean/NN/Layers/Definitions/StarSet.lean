import CORALean.ContSet.ContSet.ContSet

/-!
# The star set of CORA's constrained-zonotope propagation

CORA's `neuralNetwork` evaluates a `conZonotope` by converting it, in
`nnHelper.conversionConZonoStarSet`, to the tuple `(c, G, C, d, l, u)` and propagating that:
the points `c + G α` over the factors `α` with `C α ≤ d`, the vectors `l` and `u` bounding
the factors. The constraints are kept as a list of rows `(a, b)`, `a · α ≤ b`, which is `C` and `d`
read row by row, so a layer that adds a factor and three constraints appends to the list. The
bounds belong to the denotation: CORA's conversion computes them from the constraints, so for
a set it builds they are implied and change nothing, and a bound a step relies on is then the
bound the set already satisfies.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

structure StarSet (n : ℕ) where
  m : ℕ
  c : Fin n → ℝ
  G : Fin n → Fin m → ℝ
  cons : List ((Fin m → ℝ) × ℝ)
  l : Fin m → ℝ
  u : Fin m → ℝ

noncomputable instance (n : ℕ) : ContSet (StarSet n) (Vec ℝ n) where
  construct s := {x | ∃ α : Fin s.m → ℝ, (∀ k, s.l k ≤ α k ∧ α k ≤ s.u k) ∧
    (∀ r ∈ s.cons, ∑ k, r.1 k * α k ≤ r.2) ∧ ∀ i, x i = s.c i + ∑ k, s.G i k * α k}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
