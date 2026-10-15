module

public import CORALean.DiscrDynamics.GridPartition.GridPartition
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_HPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# `DiscrDynamics/GridPartition/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean

variable {n : ℕ}


-- ==============================  `GridPartition.multiplicator`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `multiplicator`: the number of cells in the dimensions before `i`. -/
def GridPartition.multiplicator (siz : Fin n → ℕ) (i : Fin n) : ℕ :=
  ∏ j : Fin i, siz (Fin.castLE i.is_lt.le j)


-- ===================================  `GridPartition.i2s`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `i2s`: the subscripts, from `1`, of cell `idx`, the first dimension running fastest. -/
def GridPartition.i2s (siz : Fin n → ℕ) (idx : ℕ) : Fin n → ℕ :=
  fun i => (idx - 1) / GridPartition.multiplicator siz i % siz i + 1


-- ===============================  `GridPartition.cellInterval`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The box of cell `c`, from divider `sub - 1` to divider `sub` in each dimension. -/
def GridPartition.cellInterval (P : GridPartition n) (c : ℕ) : Real.Interval (Vec ℝ n) where
  inf := fun j => P.dividers j (GridPartition.i2s P.nrOfSegments c j - 1)
  sup := fun j => P.dividers j (GridPartition.i2s P.nrOfSegments c j)


-- ===============================  `GridPartition.cellSegments`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `@partition/cellSegments`: the subscripts of each cell number. -/
def GridPartition.cellSegments (P : GridPartition n) (indexVector : List ℕ) :
    List (Fin n → ℕ) :=
  indexVector.map (GridPartition.i2s P.nrOfSegments)


-- ================================  `GridPartition.nrOfCells`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `@partition/nrOfCells`: `prod(nrOfSegments)`. -/
def GridPartition.nrOfCells (P : GridPartition n) : ℕ := ∏ j, P.nrOfSegments j


-- ==============================  `GridPartition.cellIntervals`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `@partition/cellIntervals`: the boxes of the cells given, all by default; cells out of
range are dropped, as CORA does after its message. -/
def GridPartition.cellIntervals (P : GridPartition n)
    (cellNrs : List ℕ := List.range' 1 P.nrOfCells) : List (Real.Interval (Vec ℝ n)) :=
  (cellNrs.filter fun c => 0 < c ∧ c ≤ P.nrOfCells).map P.cellInterval


-- ==============================  `GridPartition.cellPolytopes`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `@partition/cellPolytopes`: each cell box as a polytope, by halfspaces. -/
def GridPartition.cellPolytopes (P : GridPartition n)
    (cellNrs : List ℕ := List.range' 1 P.nrOfCells) : List (Real.HPolytope (Vec ℝ n)) :=
  (P.cellIntervals cellNrs).map Real.Interval.hPolytope


-- ==============================  `GridPartition.cellZonotopes`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `@partition/cellZonotopes`: each cell box as a zonotope. -/
noncomputable def GridPartition.cellZonotopes (P : GridPartition n)
    (cellNrs : List ℕ := List.range' 1 P.nrOfCells) : List (Real.Zonotope (Vec ℝ n)) :=
  (P.cellIntervals cellNrs).map Real.Interval.zonotope


-- ================================  `GridPartition.ofDividers`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `partition(dividers)`: the partition cut at the given dividers of each dimension. -/
def GridPartition.ofDividers (v : Fin n → List ℝ) : GridPartition n where
  nrOfSegments := fun j => (v j).length - 1
  dividers := fun j k => (v j).getD k 0


-- ===================================  `GridPartition.s2i`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `s2i`: the cell number of the subscripts, from `1`; `0` if one is out of range. -/
def GridPartition.s2i (siz : Fin n → ℕ) (sub : Fin n → ℕ) : ℕ :=
  if ∀ i, 0 < sub i ∧ sub i ≤ siz i then
    ∑ i, (sub i - 1) * GridPartition.multiplicator siz i + 1
  else 0


-- ===============================  `GridPartition.cellIndices`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `@partition/cellIndices`: the cell number of each subscript vector. -/
def GridPartition.cellIndices (P : GridPartition n) (subscriptVectors : List (Fin n → ℕ)) :
    List ℕ :=
  subscriptVectors.map (GridPartition.s2i P.nrOfSegments)


-- ===================================  `GridPartition.tol`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `intersectingCells`' tolerance `tol = 1e-12`. -/
noncomputable def GridPartition.tol : ℝ := 1 / 10 ^ 12


-- =================================  `GridPartition.volumeOf`  ================================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `volume(P)`: the Lebesgue volume of a set, `0` if it is infinite. -/
noncomputable def GridPartition.volumeOf (K : Set (Vec ℝ n)) : ℝ := (MeasureTheory.volume K).toReal


-- ================================  `GridPartition.cellVolume`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `volPartial`: the volume of `K` inside cell `c`. -/
noncomputable def GridPartition.cellVolume (P : GridPartition n) (K : Set (Vec ℝ n)) (c : ℕ) :
    ℝ :=
  GridPartition.volumeOf (K ∩ (P.cellInterval c).construct)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
