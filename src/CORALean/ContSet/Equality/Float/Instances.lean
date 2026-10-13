module

public import CORALean.ContSet.Capsule.Float.Theorems.IsequalSound
public import CORALean.ContSet.ConPolyZono.Float.Theorems.IsequalSound
public import CORALean.ContSet.ConZonotope.Float.Theorems.IsequalSound
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsequalSound
public import CORALean.ContSet.Interval.Float.Instances
public import CORALean.ContSet.Interval.Float.Theorems.IsequalSound
public import CORALean.ContSet.PolyZonotope.Float.Theorems.IsequalSound
public import CORALean.ContSet.Zonotope.Float.Theorems.IsequalSound

@[expose] public section

/-!
# The float representations' `isequal`

Each float representation's certified structural test is the class's `isequal`, the guarantee
being its soundness theorem; decided by the `Bool` itself.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ========================================  INSTANCES  ========================================= --

instance : Isequal (Interval (Vec 𝕋 n)) where
  isequal I J := Interval.isequal I J = true
  isequal_construct _ _ h := Interval.isequal_sound h

-- zonotope, capsule, ellipsoid
instance : Isequal (Zonotope (Vec 𝕋 n)) where
  isequal Z S := Zonotope.isequal Z S = true
  isequal_construct _ _ h := Zonotope.isequal_sound h

instance : Isequal (Capsule 𝕋 n) where
  isequal C S := Capsule.isequal C S = true
  isequal_construct _ _ h := Capsule.isequal_sound h

instance : Isequal (Ellipsoid 𝕋 n) where
  isequal E S := Ellipsoid.isequal E S = true
  isequal_construct _ _ h := Ellipsoid.isequal_sound h

-- the constrained and polynomial representations
instance : Isequal (ConZonotope 𝕋 (Vec 𝕋 n)) where
  isequal Z S := ConZonotope.isequal Z S = true
  isequal_construct _ _ h := ConZonotope.isequal_sound h

instance : Isequal (PolyZonotope (Vec 𝕋 n)) where
  isequal Z S := PolyZonotope.isequal Z S = true
  isequal_construct _ _ h := PolyZonotope.isequal_sound h

instance : Isequal (ConPolyZono 𝕋 (Vec 𝕋 n)) where
  isequal Z S := ConPolyZono.isequal Z S = true
  isequal_construct _ _ h := ConPolyZono.isequal_sound h

-- and decided by the `Bool` itself
instance : DecidableRel (Isequal.isequal (S := Interval (Vec 𝕋 n))) :=
  fun I J => inferInstanceAs (Decidable (Interval.isequal I J = true))

instance : DecidableRel (Isequal.isequal (S := Zonotope (Vec 𝕋 n))) :=
  fun Z S => inferInstanceAs (Decidable (Zonotope.isequal Z S = true))

-- the other representations likewise
instance : DecidableRel (Isequal.isequal (S := Capsule 𝕋 n)) :=
  fun C S => inferInstanceAs (Decidable (Capsule.isequal C S = true))

instance : DecidableRel (Isequal.isequal (S := Ellipsoid 𝕋 n)) :=
  fun E S => inferInstanceAs (Decidable (Ellipsoid.isequal E S = true))

instance : DecidableRel (Isequal.isequal (S := ConZonotope 𝕋 (Vec 𝕋 n))) :=
  fun Z S => inferInstanceAs (Decidable (ConZonotope.isequal Z S = true))

instance : DecidableRel (Isequal.isequal (S := PolyZonotope (Vec 𝕋 n))) :=
  fun Z S => inferInstanceAs (Decidable (PolyZonotope.isequal Z S = true))

instance : DecidableRel (Isequal.isequal (S := ConPolyZono 𝕋 (Vec 𝕋 n))) :=
  fun Z S => inferInstanceAs (Decidable (ConPolyZono.isequal Z S = true))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
