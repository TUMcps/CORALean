module

public import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
public import CORALean.ContSet.PolyZonotope.Real.Operations.ExtG

@[expose] public section

/-!
# The extended generator matrix reads back to the exact layer's

## Inputs
* `pZ` – polynomial zonotope
* `i` – row index
* `l` – column index

## Hypotheses
* none

## Conclusion
* extended generator entry reads back as the exact one
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.toReal_extG (pZ : PolyZonotope (Vec 𝕋 n)) (i : Fin n)
    (l : Fin (pZ.h + 1)) : -- --- CONCL ---
    toReal (PolyZonotope.extG pZ i l)
      = Real.PolyZonotope.extG (nominal pZ) l i := by -- --- PROOF ---
  refine Fin.cases ?_ (fun l' => ?_) l
  · simp only [PolyZonotope.extG, Real.PolyZonotope.extG, Fin.cons_zero]
    rfl
  · simp only [PolyZonotope.extG, Real.PolyZonotope.extG, Fin.cons_succ]
    rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
