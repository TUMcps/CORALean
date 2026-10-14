module

public import CORALean.ContSet.Conversion.Real.Ellipsoid_to_ConPolyZono
public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset

@[expose] public section

/-!
# An ellipsoid as a constrained polynomial zonotope, over a floating-point scalar — the construction

`Ellipsoid.conPolyZono` is the construction; `Ellipsoid_to_ConPolyZono` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.conPolyZono (E : Ellipsoid 𝕋 n) : ConPolyZono 𝕋 (Vec 𝕋 n) where
  p := E.k + 1
  h := E.k
  qI := 0
  m := 1
  q := E.k + 1
  c := E.c
  -- the ellipsoid stores its generators as a matrix, one per column
  G := fun l i => E.G i l
  E := Real.ConPolyZono.padE (Real.PolyZonotope.identE E.k) 1
  GI := Fin.elim0
  A := fun _ j => if j.val < E.k then one else neg (half one)
  b := ⟨fun _ => half one, fun _ => half one⟩
  R := fun r c => if r = c then (if c.val < E.k then 2 else 1) else 0
  I_error := E.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
