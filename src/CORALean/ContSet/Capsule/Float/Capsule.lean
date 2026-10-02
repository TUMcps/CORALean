import CORALean.ContSet.Capsule.Real.Instances
import CORALean.Global.Float.SoundFloatArithmetic

/-!
# Capsules over a floating-point scalar: the representation

The exact layer's centre, generator and radius held in `𝕋`. No error box, unlike the zonotope or
the ellipsoid: a capsule is not closed under the sum with a box (a segment thickened by a ball
and then by a box is neither a capsule nor a box), so no operation here would have anything to
pay into one, and the one that rounds, `Capsule.interval`, rounds its bounds outward instead.
`nominal` reads the stored arrays as reals, and what the capsule denotes is the exact layer's
`construct` of that, fixed by definition.

A negative stored radius denotes `∅`, as over ℝ.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Capsule (𝕋 : Type) (n : ℕ) where
  c : Vec 𝕋 n
  g : Vec 𝕋 n
  r : 𝕋

/-- The exact capsule the stored floats describe. -/
def Capsule.nominal [SoundFloatArithmetic 𝕋] (C : Capsule 𝕋 n) : CORALean.Real.Capsule n :=
  ⟨toRealVec C.c, toRealVec C.g, toReal C.r⟩

def Capsule.construct [SoundFloatArithmetic 𝕋] (C : Capsule 𝕋 n) : Set (Vec ℝ n) :=
  C.nominal.construct

instance [SoundFloatArithmetic 𝕋] : ContSet (Capsule 𝕋 n) (Vec ℝ n) := ⟨Capsule.construct⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
