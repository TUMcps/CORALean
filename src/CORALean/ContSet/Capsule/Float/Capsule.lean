module

public import CORALean.ContSet.Capsule.Real.Instances
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContSet.InflatedContSet.InflatedContSet

@[expose] public section

/-!
# Capsules over a floating-point scalar: the representation

The exact layer's center, generator and radius held in `𝕋`, plus the error box that makes it an
`InflatedContSet`: the capsule denotes its nominal part, the exact `construct` of the stored floats
read as reals, plus the box. An operation pays the difference from the exact values into the box; a
radius, itself a bound, is rounded upward. A capsule is not closed under the sum with a box, so the
box stays separate until `Capsule.absorbRounding` moves it into the radius (#185). A negative stored
radius denotes `∅`, as over ℝ.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Capsule (𝕋 : Type) (n : ℕ) where
  /-- The center, CORA's `c`. -/
  c : Vec 𝕋 n
  /-- The generator, CORA's `g`. -/
  g : Vec 𝕋 n
  /-- The radius, CORA's `r`. -/
  r : 𝕋
  /-- The error box: what rounding has cost so far. -/
  I_error : Interval (Vec 𝕋 n)

/-- The exact capsule the stored floats describe. -/
def Capsule.nominal [SoundFloatArithmetic 𝕋] (C : Capsule 𝕋 n) : CORALean.Real.Capsule n :=
  ⟨toRealVec C.c, toRealVec C.g, toReal C.r⟩

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (Capsule 𝕋 n) (CORALean.Real.Capsule n) (Vec 𝕋 n) (Vec ℝ n) where
  nominal := Capsule.nominal
  I_error C := C.I_error

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev Capsule.construct [SoundFloatArithmetic 𝕋] (C : Capsule 𝕋 n) : Set (Vec ℝ n) :=
  InflatedContSet.construct C

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
