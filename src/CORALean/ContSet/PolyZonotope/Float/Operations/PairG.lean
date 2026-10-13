import CORALean.ContSet.PolyZonotope.Float.Operations.ExtGens
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The dependent generators of a pairing, over a floating-point scalar

Generator `(i, j)` is `f` at the two extended generators, as `Real.PolyZonotope.bilinG` has it.
`f` is any function of two stored values, so that one definition serves the rounded product
(the stored generators) and the gap of its two roundings (what the error box is charged).
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {α β γ : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `f` at each pair of extended generators, the pairs indexed by `finProdFinEquiv`. -/
def PolyZonotope.pairG (f : α → β → γ) (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β) :
    Fin ((pZ₁.h + 1) * (pZ₂.h + 1)) → γ :=
  fun l => f (PolyZonotope.extGens pZ₁ (finProdFinEquiv.symm l).1)
    (PolyZonotope.extGens pZ₂ (finProdFinEquiv.symm l).2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
