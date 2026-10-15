module

public import CORALean.ContSet.Ellipsoid.Real.Instances
public import CORALean.ContSet.InflatedContSet.InflatedContSet

@[expose] public section

/-!
# Ellipsoids over a floating-point scalar: the representation

The exact layer's center and generator matrix held in `𝕋`, plus the error box
that makes it an `InflatedContSet`. Storing the generator matrix rather than
CORA's shape matrix pays here as it does over ℝ, and more: a shape matrix would
have to come back through a matrix square root, and this layer has no square
root of any kind.

No generator transpose, unlike the zonotope and the polynomial zonotope: the
exact `Ellipsoid` already stores `G` as a matrix, so the nominal part is the two
stored arrays read entrywise as reals.

What ranges over the unit ball is `u`, not a free coefficient — which changes
nothing about the rounding. `‖u‖₂ ≤ 1` gives `|uⱼ| ≤ 1`, so a rounded generator
costs exactly what a zonotope's does; `Theorems/MemGeneratorError` says why the
tighter bound is the one worth not taking.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Ellipsoid (𝕋 : Type) (n : ℕ) where
  /-- The generator count, as over ℝ: `G` is `n × k` and need not be square. -/
  k : ℕ
  c : Vec 𝕋 n
  G : Mat 𝕋 n k
  /-- The error box, the paper's `𝓘_error`. -/
  I_error : Interval (Vec 𝕋 n)

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (Ellipsoid 𝕋 n) (CORALean.Real.Ellipsoid n)
      (Vec 𝕋 n) (Vec ℝ n) where
  nominal E := ⟨E.k, toRealVec E.c, toRealMat E.G⟩
  I_error E := E.I_error

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev Ellipsoid.construct [SoundFloatArithmetic 𝕋] (E : Ellipsoid 𝕋 n) : Set (Vec ℝ n) :=
  InflatedContSet.construct E

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
