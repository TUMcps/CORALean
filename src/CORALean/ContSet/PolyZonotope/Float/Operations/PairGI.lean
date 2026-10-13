module

public import CORALean.ContSet.PolyZonotope.Float.Operations.ExtGens
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# The independent generators of a pairing, over a floating-point scalar

The three blocks `Real.PolyZonotope.bilinGI` carries, in its order: the independent generators of
the first set with the extended generators of the second, independent with independent, extended
generators of the first with the independent ones of the second. `f` is any function of two
stored values, as in `pairG`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {α β γ : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The pairs `f (GI₁ j) (ext₂ l)`, `f (GI₁ j) (GI₂ l)`, `f (ext₁ l) (GI₂ j)` as one list. -/
def PolyZonotope.pairGI (f : α → β → γ) (pZ₁ : PolyZonotope α) (pZ₂ : PolyZonotope β) :
    Fin (pZ₁.q * (pZ₂.h + 1) + pZ₁.q * pZ₂.q + (pZ₁.h + 1) * pZ₂.q) → γ :=
  Fin.append
    (Fin.append
      (fun l => f (pZ₁.GI (finProdFinEquiv.symm l).1)
        (PolyZonotope.extGens pZ₂ (finProdFinEquiv.symm l).2))
      (fun l => f (pZ₁.GI (finProdFinEquiv.symm l).1) (pZ₂.GI (finProdFinEquiv.symm l).2)))
    (fun l => f (PolyZonotope.extGens pZ₁ (finProdFinEquiv.symm l).1)
      (pZ₂.GI (finProdFinEquiv.symm l).2))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
