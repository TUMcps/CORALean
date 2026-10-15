module

public import CORALean.ContSet.InflatedContSet.InflatedContSet
public import CORALean.ContSet.PolyZonotope.Real.Instances

@[expose] public section

/-!
# Sparse polynomial zonotopes over a floating-point scalar: the representation

CORA's `polyZonotope` with its centre, dependent generators, exponent matrix and
independent generators, plus the error box that makes it an `InflatedContSet`.
The nominal part is the polynomial zonotope those stored floats describe; the
box holds what rounding has cost.

Only `c`, `G` and `GI` move to `𝕋`. The exponent matrix stays over ℕ, where
every operation on it — block-diagonal append, column addition, column
deletion — is exact, so the monomials of the nominal set are the exact layer's
monomials and not roundings of them. That is what makes the float layer's error
identical in kind to a zonotope's; `Theorems/MemGeneratorError` says what it
costs.

The error box is `I_error`, the paper's `𝓘_error`.

`PolyZonotope α` is generic over its ambient type, generators a family, as the exact
layer's `PolyZonotope α` is; its vector case is `PolyZonotope (Vec 𝕋 n)`.
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

structure PolyZonotope (α : Type) where
  /-- The dependent factors, shared across all of `G`. -/
  p : ℕ
  /-- The dependent generators. -/
  h : ℕ
  /-- The independent generators. -/
  q : ℕ
  c : α
  G : Fin h → α
  E : Fin p → Fin h → ℕ
  GI : Fin q → α
  I_error : Interval α

/-- The exact polynomial zonotope the stored floats describe, read through `RealImage`. -/
protected abbrev PolyZonotope.nominal {α β : Type} [RealImage α β] (pZ : PolyZonotope α) :
    CORALean.Real.PolyZonotope β :=
  ⟨pZ.p, pZ.h, pZ.q, RealImage.realImage pZ.c, fun l => RealImage.realImage (pZ.G l), pZ.E,
    fun j => RealImage.realImage (pZ.GI j)⟩

instance {α β : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] :
    InflatedContSet (PolyZonotope α) (CORALean.Real.PolyZonotope β) α β where
  nominal := PolyZonotope.nominal
  I_error pZ := pZ.I_error

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev PolyZonotope.construct [SoundFloatArithmetic 𝕋] (pZ : PolyZonotope (Vec 𝕋 n)) :
    Set (Vec ℝ n) := InflatedContSet.construct pZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
