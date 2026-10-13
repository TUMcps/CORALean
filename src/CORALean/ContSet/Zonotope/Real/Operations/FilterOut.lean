import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# `Zonotope.filterOut`

CORA's `@zonotope/filterOut(Z)` [1]: from a list of parallelotopes, delete those "covered by
other parallelotopes". For each cell `Z{ind}` it forms `Pint = P_ind \ P_j` for every other `j`
(set differences of `polytope(Z{i})`) and keeps the cell if `chebyball(Pint)` has radius
`≠ -inf`, that is, if the remainder `P_ind \ ⋃_{j ≠ ind} P_j` is nonempty (CORA's `mldivide`
returns only full-dimensional pieces, so a lower-dimensional remainder is dropped as well).

What is formalized is that criterion: the indices of the cells whose remainder after the union of
all the others has nonempty interior. CORA's sort by volume only orders the output list and is
not modelled. The method does not run in CORA (`chebyball` is not a function of the toolbox) and
its criterion does not preserve the union (FINDINGS.md); `filterOut_covered` is what a deletion
does guarantee, `filterOut_pair` what it does not.

## References

* [1] `contSet/@zonotope/filterOut.m`, CORA (Sep. 2025), by M. Althoff (2008). No paper behind the
      rule was confirmed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The cells that survive CORA's `filterOut`: those with a remainder of nonempty interior once
every other cell is removed (`Pint = P_ind \ P_j` over all `j ≠ ind`, `chebyball(Pint)`). -/
def Zonotope.filterOut (Zs : Fin m → Zonotope (Vec ℝ n)) : Set (Fin m) :=
  {ind | (interior ((Zs ind).construct \ ⋃ j ∈ {j | j ≠ ind}, (Zs j).construct)).Nonempty}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
