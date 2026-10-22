module

public import CORALean.ContSet.ConZonotope.Real.Instances
public import CORALean.ContSet.HPolytope.Float.HPolytope
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# Constrained zonotopes over a floating-point scalar: the representation

CORA's `conZonotope` [1, Def. 3] with center, generators and coefficient constraints held in `𝕋`,
plus the error box that makes it an `InflatedContSet`. `ConZonotope 𝕋 α` is generic over its ambient
type, as the exact layer's is; the constraints live on `Vec 𝕋 h`. The vector case is
`ConZonotope 𝕋 (Vec 𝕋 n)`. Rounding is paid where the representation has slack of the same kind: the
center and generators have none, so theirs goes into the ambient box; the constraints have slack in
their bounds, so theirs goes into `P`'s rows (an equality is kept where a certificate pays the move
into the box, `ConZonotope.anchorSlab`, else it becomes two inequalities, `HPolytope.slab`). One
box, not two: only `P`'s nominal part is read; its own box stays at the origin.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
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

/-- A constrained zonotope over floats: center `c`, `h` generators `G`, the halfspace constraint `P`
on the coefficients, and the error box `I_error` that rounding has cost. -/
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

/-- A float constrained zonotope inflates the real one its stored floats describe, the `nominal`
one. -/
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
