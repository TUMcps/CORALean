import CORALean.ContSet.PolyZonotope.Float.Operations.QuadMap
import CORALean.ContSet.PolyZonotope.Real.Operations.ExtG

/-!
# The extended generator matrix reads back to the exact layer's
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.toReal_extG (pZ : PolyZonotope (Vec 𝕋 n)) (i : Fin n) (l : Fin (pZ.h + 1)) :
    toReal (PolyZonotope.extG pZ i l)
      = Real.PolyZonotope.extG (nominal pZ) l i := by -- --- PROOF ---
  refine Fin.cases ?_ (fun l' => ?_) l
  · simp only [PolyZonotope.extG, Real.PolyZonotope.extG, Fin.cons_zero]
    rfl
  · simp only [PolyZonotope.extG, Real.PolyZonotope.extG, Fin.cons_succ]
    rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
