import CORALean.ContSet.Zonotope.Real.Operations.EncloseManyDropped

/-!
# `Zonotope.encloseManyBasis`

The rotation `rotMatrix` of CORA's `@zonotope/encloseMany`: the unit vector
`newGen = direction / ‖direction‖₂` as first column, followed by the axes, with
the axis most aligned with `newGen` left out (`encloseManyDropped`). Dropping that axis is what
keeps the matrix invertible: `newGen` has a nonzero entry there, and nowhere else is needed.

CORA sorts the alignments and keeps the remaining axes in increasing order of
alignment; here they keep their own order. The enclosure `R · box(R⁻¹ ·)` is
unchanged by a permutation of `R`'s columns, so only the choice of the dropped
axis matters, and among several equally aligned axes any maximiser does (CORA
drops the last in its sort order).

Source: [1].

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

variable {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `rotMatrix = [newGen, orient(:,pickedIndices)]`: `newGen` as the first column, then
every standard axis but the dropped one. -/
noncomputable def Zonotope.encloseManyBasis (direction : Vec ℝ (m + 1)) : Mat ℝ (m + 1) (m + 1) :=
  let newGen : Vec ℝ (m + 1) := (Real.sqrt (direction ⬝ᵥ direction))⁻¹ • direction
  let dropped := Zonotope.encloseManyDropped direction
  Matrix.of fun i => Fin.cons (newGen i) (fun j => if i = dropped.succAbove j then (1 : ℝ) else 0)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
