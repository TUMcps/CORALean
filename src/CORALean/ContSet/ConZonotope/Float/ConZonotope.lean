module

public import CORALean.ContSet.ConZonotope.Real.Instances
public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# Constrained zonotopes over a floating-point scalar: the representation

CORA's `conZonotope` with its centre, generators and coefficient constraints all
held in `𝕋`, plus the error box that makes it an `InflatedContSet`. `ConZonotope 𝕋 α`
is generic over its ambient type, generators a family, as the exact layer's
`ConZonotope α` is; `𝕋` stays, the constraints living on the coefficient space
`Vec 𝕋 h` at every ambient type. The vector case is `ConZonotope 𝕋 (Vec 𝕋 n)`.

Two roundings, in two different places, and the rule is the same one the other
representations follow: pay where the representation already has slack of the
same kind. The centre and the generators have none — paying into them would grow
the order at every operation — so their rounding goes into the ambient box. The
constraints have slack in their bounds, so theirs goes into `P`'s rows; a rounded
equality is kept where a certificate pays the move onto it into the ambient box
(`ConZonotope.anchorSlab`), and becomes two inequalities (`HPolytope.slab`) otherwise.

One box, therefore, not two: `P` is a float `HPolytope`, but only its nominal part is
read, and the operations leave its own box at the origin.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure ConZonotope (𝕋 α : Type) where
  h : ℕ
  c : α
  G : Fin h → α
  P : HPolytope 𝕋 (Vec 𝕋 h)
  I_error : Interval α

/-- The exact constrained zonotope the stored floats describe, read through `RealImage`. -/
protected abbrev ConZonotope.nominal {α β : Type} [RealImage α β] [SoundFloatArithmetic 𝕋]
    (cZ : ConZonotope 𝕋 α) : CORALean.Real.ConZonotope β :=
  ⟨cZ.h, RealImage.realImage cZ.c, fun j => RealImage.realImage (cZ.G j), cZ.P.nominal⟩

instance {α β : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] [SoundFloatArithmetic 𝕋] :
    InflatedContSet (ConZonotope 𝕋 α) (CORALean.Real.ConZonotope β) α β where
  nominal := ConZonotope.nominal
  I_error cZ := cZ.I_error

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev ConZonotope.construct [SoundFloatArithmetic 𝕋] (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    Set (Vec ℝ n) :=
  InflatedContSet.construct cZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
