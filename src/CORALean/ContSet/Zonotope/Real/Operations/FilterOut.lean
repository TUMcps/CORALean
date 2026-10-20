module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

/-!
# `Zonotope.filterOut`

CORA's `@zonotope/filterOut(Z)` [1]: from a list of parallelotopes, delete those "covered by
other parallelotopes". For each cell `Z{ind}` it forms `Pint = P_ind \ P_j` for every other `j`
and keeps the cell if `chebyball(Pint)` has radius `≠ -inf`, that is, if the remainder
`P_ind \ ⋃_{j ≠ ind} P_j` is nonempty (lower-dimensional remainders are dropped as well).
Formalized is that criterion: the indices of the cells whose remainder has nonempty interior.
The method does not run in CORA (`chebyball` is no function of the toolbox) and its criterion does
not preserve the union (`references/coverage/contSet/zonotope.md`, row `filterOut`); see
`filterOut_covered`, `filterOut_pair`.

## Inputs
* `Zs` – cells

## Output
* indices of the cells that survive

## References

* [1] `contSet/@zonotope/filterOut.m`, CORA (Sep. 2025), by M. Althoff (2008). No paper behind the
      rule was confirmed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


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
