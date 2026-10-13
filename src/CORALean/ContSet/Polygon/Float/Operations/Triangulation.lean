module

public import CORALean.ContSet.Polygon.Float.Polygon

@[expose] public section

/-!
# `Polygon.triangulation`, over a floating-point scalar

The vertex triangles of every float piece, as over ℝ: for each triple `(a, b, c)` of a piece's
vertices the piece with those three vertices and the piece's own error box. Nothing is computed
on the vertices, so nothing rounds, and the box stays what it was.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The vertex triangles of every piece, each with its piece's error box. -/
def Polygon.triangulation (P : Polygon 𝕋) : Polygon 𝕋 :=
  ⟨P.sets.flatMap fun p => (List.finRange p.k).flatMap fun a => (List.finRange p.k).flatMap
    fun b => (List.finRange p.k).map fun c => ⟨3, ![p.V a, p.V b, p.V c], p.E⟩⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
