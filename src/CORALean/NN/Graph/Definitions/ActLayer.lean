module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# The enclosure of an activation layer on matrix polynomial zonotopes

[1, Prop. 1]: for an elementwise activation layer, `enclose` returns an outer-approximative output
set with at most one more generator per output neuron, which [1] takes from Kochdumper et al.
(2023) and does not prove. `ActLayer` is any such enclosure, a map on matrix polynomial
zonotopes that keeps the factor count (new coefficients are independent generators).
`Encloses σ` says it encloses `σ` applied entrywise *at the factor vector*, with a coefficient
for each independent generator it adds: the dependency the next convolution needs to see, and
what the enclosure of [1, Prop. 1] gives. `AddsAtMost n` is the count, `n` the layer's neurons.

## References

* [1] [T. Ladner, M. Eichelbeck and M. Althoff. "Formal Verification of Graph Convolutional Networks
      with Uncertain Node Features and Uncertain Graph Structure". Transactions on Machine Learning
      Research, 2025.](../../../../../references/2025/ladner-tmlr-gcn.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N F : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- An enclosure of an activation layer: a map of matrix polynomial zonotopes that keeps `p`. -/
structure GNN.ActLayer (N F : ℕ) where
  act : PolyZonotope (Mat ℝ N F) → PolyZonotope (Mat ℝ N F)
  p_eq : ∀ S, (act S).p = S.p

/-- At every factor vector of a set without independent generators, `σ` applied entrywise is a
point of the enclosure at that vector, up to coefficients of the generators it adds. -/
def GNN.ActLayer.Encloses (A : GNN.ActLayer N F) (σ : ℝ → ℝ) : Prop :=
  ∀ S : PolyZonotope (Mat ℝ N F), S.q = 0 → ∀ a : Fin S.p → ℝ, (∀ k, |a k| ≤ 1) →
    ∃ β : Fin (A.act S).q → ℝ, (∀ j, |β j| ≤ 1) ∧
      (S.point a).map σ = (A.act S).point (fun k => a (Fin.cast (A.p_eq S) k))
        + ∑ j, β j • (A.act S).GI j

/-- The enclosure adds at most `n` generators. -/
def GNN.ActLayer.AddsAtMost (A : GNN.ActLayer N F) (n : ℕ) : Prop :=
  ∀ S : PolyZonotope (Mat ℝ N F), (A.act S).h + (A.act S).q ≤ S.h + S.q + n

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
