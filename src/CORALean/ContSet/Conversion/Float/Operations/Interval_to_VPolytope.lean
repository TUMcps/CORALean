module

public import CORALean.ContSet.VPolytope.Float.VPolytope
public import CORALean.ContSet.Conversion.Real.Interval_to_VPolytope

@[expose] public section

/-!
# A box as its corners, over a floating-point scalar — the construction

`Interval.vPolytope` is the construction; `Interval_to_VPolytope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.vPolytope (I : Interval (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) where
  k := 2 ^ n
  V := fun l i => if signEquiv n l i then I.sup i else I.inf i
  I_error := ⟨fun _ => zero, fun _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
