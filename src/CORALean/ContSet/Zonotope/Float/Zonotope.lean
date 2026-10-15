module

public import CORALean.ContSet.InflatedContSet.InflatedContSet
public import CORALean.ContSet.Zonotope.Real.Instances

@[expose] public section

/-!
# Zonotopes over a floating-point scalar: the representation

CORA's `zonotope` with its centre and generators, plus the error box that makes
it an `InflatedContSet`. The nominal part is the zonotope those stored floats
describe; the box holds what rounding has cost.

`Zonotope α` is indexed by the ambient type it stores, as the exact layer's
`Zonotope α` and the float `Interval α` are, with generators a family rather than
a matrix: `Zonotope (Mat 𝕋 m n)` is CORA's `matZonotope`, with no separate
representation. `Zonotope (Vec 𝕋 n)` is the vector case, and an algorithm generic
over the dimension takes the family `fun k => Zonotope (Vec 𝕋 k)`. A matrix
operation whose vector namesake means something else carries a `mat` prefix, as
`Zonotope.matInterval` does.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Zonotope (α : Type) where
  h : ℕ
  c : α
  G : Fin h → α
  I_error : Interval α

/-- The exact zonotope the stored floats describe, read through `RealImage`. -/
protected abbrev Zonotope.nominal {α β : Type} [RealImage α β] (Z : Zonotope α) :
    CORALean.Real.Zonotope β :=
  ⟨Z.h, RealImage.realImage Z.c, fun j => RealImage.realImage (Z.G j)⟩

instance {α β : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] :
    InflatedContSet (Zonotope α) (CORALean.Real.Zonotope β) α β where
  nominal := Zonotope.nominal
  I_error Z := Z.I_error

/-- Inherited from `InflatedContSet`, at any ambient type: `nominal + I_error`. -/
abbrev Zonotope.construct {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β]
    [Entrywise β ι] (Z : Zonotope α) : Set β :=
  InflatedContSet.construct Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
