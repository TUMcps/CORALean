import CORALean.ContSet.PolyZonotope.Float.Theorems.SubsMulRel
import CORALean.ContSet.PolyZonotope.Float.Operations.SubsPow
import CORALean.ContSet.PolyZonotope.Real.Operations.SubsPow

/-!
# `subsPow` keeps the bracket

The empty product is `1` on both sides, a power is a product with the previous one (`subsMul_rel`).
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.subsPow_rel {A : List ((𝕋 × 𝕋) × (Fin p → ℕ))}
    {A' : List (ℝ × (Fin p → ℕ))} (hA : PolyZonotope.subsRel A A') (d : ℕ) :
    PolyZonotope.subsRel (PolyZonotope.subsPow A d) (Real.PolyZonotope.subsPow A' d) := by
  induction d with
  | zero =>
    exact List.Forall₂.cons ⟨rfl, by simp [toReal_one]⟩ List.Forall₂.nil
  | succ d ih => exact PolyZonotope.subsMul_rel hA ih

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
