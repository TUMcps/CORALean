import CORALean.ContSet.Capsule.Float.Capsule

/-!
# `Capsule.project` over a floating-point scalar

Centre and generator read at `dims`, the radius unchanged, as over ℝ. Nothing is computed, so
nothing is rounded.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Capsule.project (C : Capsule 𝕋 n) (dims : Fin m → Fin n) : Capsule 𝕋 m where
  c := fun i => C.c (dims i)
  g := fun i => C.g (dims i)
  r := C.r

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
