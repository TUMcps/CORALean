import CORALean.ContSet.Zonotope.Real.Operations.EncloseManyBasis
import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard
import CORALean.ContSet.Zonotope.Real.Operations.Mtimes
import CORALean.ContSet.Conversion.Real.Zonotope_to_Interval
import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# `Zonotope.encloseMany`

CORA's `@zonotope/encloseMany(Z, direction)` [1]: one oriented box around a list of zonotopes.
Each cell is reduced to a parallelotope, its corners are taken to the frame `R` whose first axis
is `direction`, the box of all corners there is the interval hull, and the box is rotated back.

The reduction CORA names, `reduce(Z{i}, 'parallelpiped')`, does not exist (FINDINGS.md): its
`otherwise` branch throws, so the method errors on every input. What is formalized is the
enclosure it was written for, with the parallelotope taken to be Girard's order-one reduction
`reduceGirard 1`, which is a parallelotope (`n` generators) and an outer approximation. The
corners of a zonotope fill its interval hull, so the box of the corners is `Zonotope.interval`
of the rotated parallelotope, and the box of all cells is the componentwise `min`/`max`.

At least one cell is required (`Fin (q + 1)`): CORA's `enclosePoints` of an empty point list
errors.

## References

* [1] `contSet/@zonotope/encloseMany.m`, CORA (Sep. 2025). No paper behind the
      rule was confirmed.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


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
