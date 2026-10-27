module

public import CORALean.ContSet.InflatedContSet.Interfaces
public import CORALean.ContSet.PolyZonotope.Real.Instances

@[expose] public section

/-!
# Sparse polynomial zonotopes over a floating-point scalar: the representation

CORA's `polyZonotope` [1, Def. 1] with its center, dependent generators, exponent matrix and
independent generators, plus the error box `I_error` (the paper's `𝓘_error`) that makes it an
`InflatedContSet`. The nominal part is the polynomial zonotope those stored floats describe; the box
holds what rounding has cost. Only `c`, `G` and `GI` move to `𝕋`. The exponent matrix stays over ℕ,
where every operation on it (block-diagonal append, column addition, column deletion) is exact, so
the monomials are the exact layer's, and the float error is identical in kind to a zonotope's
(`Theorems/MemGeneratorError`). `PolyZonotope α` is generic over its ambient type, as the exact
layer's is; its vector case is `PolyZonotope (Vec 𝕋 n)`.

## References

* [1] [N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set Representation for
      Reachability Analysis". IEEE Transactions on Automatic Control,
      2021.](../../../../../references/2021/kochdumper-tac-sparse-polyzonotopes.md)
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

/-- A sparse polynomial zonotope over floats: center `c`, `h` dependent generators `G` with exponent
matrix `E` over `p` factors, `q` independent generators `GI`, and the error box `I_error`. -/
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

/-- A float polynomial zonotope inflates the real one its stored floats describe, the `nominal` one.
-/
instance {α β : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β] :
    InflatedContSet (PolyZonotope α) (CORALean.Real.PolyZonotope β) α β where
  nominal := PolyZonotope.nominal
  I_error pZ := pZ.I_error

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev PolyZonotope.construct [SoundFloatArithmetic 𝕋] (pZ : PolyZonotope (Vec 𝕋 n)) :
    Set (Vec ℝ n) := InflatedContSet.construct pZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
