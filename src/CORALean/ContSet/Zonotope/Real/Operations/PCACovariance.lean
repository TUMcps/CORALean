module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Partition

@[expose] public section

/-!
# `Zonotope.pcaCovariance`

The scatter matrix of the generators a partition drops: entry `(i, j)` is `∑ l, g_l i * g_l j`,
which is `G Gᵀ` at the dropped block. Symmetric by construction, the hypothesis a spectral
decomposition needs (`pcaCovariance_isHermitian`). CORA builds the point cloud `[G, -G]` and
calls `cov` on its transpose [1], as [2, Alg. 2] does. That cloud has zero mean, so the centering
subtracts nothing and what remains is `V Vᵀ / (2r - 1)`, `2 / (2r - 1)` times the matrix here. The
factor is dropped: it is positive wherever CORA reaches this line (it returns early when nothing
is dropped), and a positive scalar moves no eigenspace.

## Inputs
* `Z` – zonotope
* `part` – split of the generators

## Output
* scatter matrix of the dropped generators

## References

* [1] `contSet/@zonotope/private/priv_reducePCA.m`, CORA (Sep. 2025). No paper
      behind the rule was confirmed.
* [2] [A.-K. Kopetzki, B. Schürmann and M. Althoff. "Methods for Order Reduction of Zonotopes". 2017
      IEEE 56th Annual Conference on Decision and Control (CDC),
      2017.](../../../../../../references/2017/kopetzki-cdc-order-reduction.md)
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The scatter matrix `G Gᵀ` of the generators a partition drops, CORA's
covariance up to the positive factor its `cov` divides by. -/
def Zonotope.pcaCovariance (Z : Zonotope (Vec ℝ n))
    (part : Split (Fin Z.h) into (Fin q) ⊕ (Fin r)) : Mat ℝ n n :=
  Matrix.of fun i j => ∑ l, Z.G (part.right l) i * Z.G (part.right l) j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
