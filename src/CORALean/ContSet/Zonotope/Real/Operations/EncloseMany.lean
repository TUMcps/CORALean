module

public import CORALean.ContSet.Zonotope.Real.Operations.EncloseManyBasis
public import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# `Zonotope.encloseMany`

CORA's `@zonotope/encloseMany(Z, direction)` [1]: one oriented box around a list of zonotopes.
Each cell is reduced to a parallelotope, its corners are taken to the frame `R` whose first axis
is `direction`, the box of all corners there is the interval hull, and the box is rotated back.
The reduction CORA names, `reduce(Z{i}, 'parallelpiped')`, does not exist
(`references/coverage/contSet/zonotope.md`, row `encloseMany`): the method errors on every input.
What is formalized is the enclosure it was written for, with the parallelotope taken to be
Girard's order-one reduction `reduceGirard 1`. At least one cell is required (`Fin (q + 1)`):
CORA's `enclosePoints` of an empty point list errors.

## Inputs
* `Zs` – cells to enclose
* `direction` – main direction

## Output
* oriented box around the parallelotope reductions

## References

* [1] `contSet/@zonotope/encloseMany.m`, CORA (Sep. 2025). No paper behind the
      rule was confirmed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `encloseMany(Z, direction)`: the oriented box, in the frame whose first axis is
`direction`, around the parallelotope reductions of the cells `Zs`. -/
noncomputable def Zonotope.encloseMany (Zs : Fin (q + 1) → Zonotope (Vec ℝ (m + 1)))
    (direction : Vec ℝ (m + 1)) : Zonotope (Vec ℝ (m + 1)) :=
  let rotMatrix := Zonotope.encloseManyBasis direction                  -- [newGen, picked axes]
  let rotMatrixInv := rotMatrix⁻¹                                         -- inv(rotMatrix)
  let Zred := fun i => (Zs i).reduceGirard 1                            -- the parallelotope of Z{i}
  let rotated := fun i => Zonotope.mtimes rotMatrixInv (Zred i)         -- rotMatrix \ vertices
  let I : Interval (Vec ℝ (m + 1)) :=                                    -- interval.enclosePoints
    { inf := fun k => Finset.univ.inf' ⟨0, Finset.mem_univ _⟩ fun i => (rotated i).interval.inf k
      sup := fun k => Finset.univ.sup' ⟨0, Finset.mem_univ _⟩ fun i => (rotated i).interval.sup k }
  let Z := I.zonotope                                                     -- zonotope(I)
  Zonotope.mtimes rotMatrix Z                                             -- rotMatrix * Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
