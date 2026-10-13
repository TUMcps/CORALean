module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Partition

@[expose] public section

/-!
# `Zonotope.pcaCovariance`

The scatter matrix of the generators a partition drops: entry `(i, j)` is
`∑ l, g_l i * g_l j`, which is `G Gᵀ` at the dropped block. Symmetric by
construction, and that symmetry is the whole point of the definition — it is
the hypothesis a spectral decomposition needs, and `pcaCovariance_isHermitian`
is where it is discharged.

CORA builds the point cloud `[G, -G]` and calls `cov` on its transpose [1], as
[2, Alg. 2] does. That cloud has zero mean, as the file's own comment records, so the centring
`cov` performs subtracts nothing and what remains is `V Vᵀ / (2r - 1)`, which
is `2 / (2r - 1)` times the matrix here. The factor is dropped: it is positive
wherever CORA reaches this line — CORA returns early when nothing is dropped —
and a positive scalar moves no eigenspace, so the principal axes are the same
axes.

## References

* [1] `contSet/@zonotope/private/priv_reducePCA.m`, CORA (Sep. 2025). No paper
      behind the rule was confirmed.
* [2] A.-K. Kopetzki, B. Schürmann and M. Althoff. "Methods for Order Reduction of
      Zonotopes". In Proc. of the 56th IEEE Conference on Decision and Control (CDC), pp.
      5626-5633, 2017.
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
