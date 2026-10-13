module

public import CORALean.ContSet.Conversion.Float.ZonoBundle_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Zonotope_to_Interval

@[expose] public section

/-!
# A bundle's box, at one component, over a floating-point scalar

Through `ZonoBundle.zonotope i`, then that zonotope's own box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

def ZonoBundle.interval (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) : Interval (Vec 𝕋 n) :=
  (zB.zonotope i).interval


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.interval_contains (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.interval i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.interval_contains _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
