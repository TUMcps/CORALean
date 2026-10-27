module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import CORALean.Global.Partition

@[expose] public section

/-!
# `PolyZonotope.dropIndepMat`

[1, Prop. 2]'s `P`: the picked dependent generators `ind_1, …, ind_n`, read off
by `partD.left`, laid out as columns of a square matrix. Named on its own
because `dropIndepStretch` and its outer theorem both need it, one to invert
and one to state invertibility of.

## Inputs
* `pZ` – polynomial zonotope
* `r` – number of dropped generators
* `partD` – split of the dependent generators

## Output
* square matrix of the kept dependent generators

## References

* [1] [M. Althoff. "Reachability Analysis of Nonlinear Systems using Conservative Polynomialization
      and Non-Convex Sets". Proceedings of the 16th international conference on Hybrid systems:
      computation and control,
      2013.](../../../../../../references/2013/althoff-hscc-conservative-polynomialization.md)
-/

-- Authors:       Claude Opus 5
-- Written:       21-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The picked dependent generators, as the columns of a square matrix. -/
def PolyZonotope.dropIndepMat (pZ : PolyZonotope (Vec ℝ n)) {r : ℕ}
    (partD : Split (Fin pZ.h) into (Fin n) ⊕ (Fin r)) : Mat ℝ n n :=
  Matrix.of (fun a b => pZ.G (partD.left b) a)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
