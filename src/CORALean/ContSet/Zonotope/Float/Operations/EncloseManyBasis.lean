module

public import CORALean.ContSet.Zonotope.Float.Operations.EncloseManyDropped

@[expose] public section

/-!
# `Zonotope.encloseManyBasis`, over a floating-point scalar

The rotation `rotMatrix` of CORA's `@zonotope/encloseMany`: the unit vector `newGen` as first
column, followed by the standard axes, with the axis most aligned with `newGen` left out
(`encloseManyDropped`). Every entry is a stored float, `newGen`'s or an exact `0` or `1`, so the
matrix is exactly the one it is read as. Dropping that axis keeps it invertible when `newGen` is
nonzero there. As over ℝ the remaining axes keep their own order, where CORA sorts them by
alignment; the enclosure `R box(R⁻¹ ·)` does not depend on the order of `R`'s columns.

Source: [1].

## References

* [1] `contSet/@zonotope/encloseMany.m`, CORA (Sep. 2025). No paper behind the
      rule was confirmed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `rotMatrix = [newGen, orient(:,pickedIndices)]`: `newGen` as the first column, then
every standard axis but the dropped one. -/
def Zonotope.encloseManyBasis (newGen : Vec 𝕋 (m + 1)) : Mat 𝕋 (m + 1) (m + 1) :=
  let dropped := Zonotope.encloseManyDropped newGen
  Matrix.of fun i => Fin.cons (newGen i) (fun j => if i = dropped.succAbove j then one else zero)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
