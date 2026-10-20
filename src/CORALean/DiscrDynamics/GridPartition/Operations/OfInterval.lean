module

public import CORALean.DiscrDynamics.GridPartition.Operations.Basic

@[expose] public section

/-!
# `GridPartition.ofInterval`

CORA's `partition(interval, nrOfSegments)`: the box cut evenly, `linspace(inf, sup, m + 1)` in
each dimension. `linspace` ends exactly on `sup`; with no segment it returns `sup` alone, so a
partition with a dimension of `0` segments is not a box and the constructor is for `m ≥ 1`.

## Inputs
* `I` – box
* `segs` – segments per dimension

## Output
* partition of the box into equal cells
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `partition(I, segs)`: dimension `j` is cut at `inf + k (sup - inf) / segs j`. -/
noncomputable def GridPartition.ofInterval (I : Real.Interval (Vec ℝ n)) (segs : Fin n → ℕ) :
    GridPartition n where
  nrOfSegments := segs
  dividers := fun j k =>
    if k = segs j then I.sup j else I.inf j + k * ((I.sup j - I.inf j) / segs j)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
