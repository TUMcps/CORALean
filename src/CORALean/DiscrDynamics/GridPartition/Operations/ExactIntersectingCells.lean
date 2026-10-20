module

public import CORALean.DiscrDynamics.GridPartition.Operations.IntersectingCellsOf
public import CORALean.DiscrDynamics.GridPartition.Definitions.Basic

@[expose] public section

/-!
# `GridPartition.exactIntersectingCells`

CORA's `@partition/exactIntersectingCells(Obj, contSet)`: the cells that share positive volume
with the set `P`, `iS`, led by `0`, and the share `iProp` of `P`'s volume in the outside and in
each cell. The candidates are `intersectingCells`; each is intersected with `P` and measured, here
as the Lebesgue measure of the denoted sets. A set of volume `0` (or `∞`, which CORA would divide
by) gets `iS = 0` and `iProp = 1`, as in CORA. The `'probability error'` message is not.

## Inputs
* `P` – grid partition
* `X` – set

## Output
* intersecting cells with the volume share of each
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [Real.IntervalOuter S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `exactIntersectingCells(P, X)`: positive-volume cells and the volume share in each. -/
noncomputable def GridPartition.exactIntersectingCells (P : GridPartition n) (X : S n) :
    GridPartition.Proportions :=
  if 0 < GridPartition.volumeOf (ContSet.construct X) then
    let volTotal := GridPartition.volumeOf (ContSet.construct X)
    let cellIndices := P.intersectingCellsOf X
    -- `cellPolytopes` drops cell `0`, the outside, so only real cells are intersected
    let checked := cellIndices.filter fun c => 0 < c ∧ c ≤ P.nrOfCells
    let iS := checked.filter fun c => 0 < P.cellVolume (ContSet.construct X) c
    let iProp := (List.range' 1 P.nrOfCells).map fun c =>
      if c ∈ iS then P.cellVolume (ContSet.construct X) c / volTotal else 0
    ⟨0 :: iS, (1 - iProp.sum) :: iProp⟩
  else ⟨[0], [1]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
