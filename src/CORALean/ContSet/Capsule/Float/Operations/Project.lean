module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Capsule.project` over a floating-point scalar

Center, generator and error box read at `dims`, the radius unchanged, as over ℝ. Nothing is
computed, so nothing is rounded.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.project (C : Capsule 𝕋 n) (dims : Fin m → Fin n) : Capsule 𝕋 m where
  c := fun i => C.c (dims i)
  g := fun i => C.g (dims i)
  r := C.r
  I_error := C.I_error.project dims

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
