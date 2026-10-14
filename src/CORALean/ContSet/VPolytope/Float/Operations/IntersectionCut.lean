module

public import CORALean.ContSet.Conversion.Float.VPolytope_to_HPolytope
public import CORALean.ContSet.HPolytope.Float.Operations.ContractBox
public import CORALean.ContSet.VPolytope.Float.Operations.Intersection

@[expose] public section

/-!
# `VPolytope.intersectionCut`, over a floating-point scalar

The tighter sibling of `VPolytope.intersection`. Each operand goes out to halfspaces on
the caller's directions (`VPolytope.hPolytope`, bounds rounded outward), and the two boxes'
intersection is cut to those rows one after another (`HPolytope.contractBox`). The result is
still the corners of a box, since nothing here enumerates vertices; but the box is the cut
one, never larger than the boxes' intersection and, where the directions include the
operands' facet normals, much smaller.

Nothing is solved: a row is cut by one interval evaluation, and soundness is that of the
conversion and of the cut, each proved elsewhere.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q₁ q₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The boxes' intersection cut to both operands' halfspaces on the directions `Aq₁`, `Aq₂`. -/
def VPolytope.intersectionCut (P₁ P₂ : VPolytope (Vec 𝕋 n)) (Aq₁ : Mat 𝕋 q₁ n)
    (Aq₂ : Mat 𝕋 q₂ n) : VPolytope (Vec 𝕋 n) :=
  Interval.vPolytope
    ((P₂.hPolytope Aq₂).contractBox ((P₁.hPolytope Aq₁).contractBox
      (P₁.interval.intersection P₂.interval)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
