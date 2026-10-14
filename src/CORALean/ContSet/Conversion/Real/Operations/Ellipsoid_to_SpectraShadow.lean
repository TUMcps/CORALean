module

public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# An ellipsoid as a spectrahedral shadow — the construction

`Ellipsoid.spectraShadow` is the construction; `Ellipsoid_to_SpectraShadow` states and proves what
it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The ellipsoid as the shadow of `‖u‖₂ ≤ 1`, the ball written as one linear matrix
inequality of size `k + 1`. -/
def Ellipsoid.spectraShadow (E : Ellipsoid n) : SpectraShadow (Vec ℝ n) where
  k := E.k + 1
  m := E.k
  A₀ := 1
  A := fun i => Matrix.of fun p q =>
    if (p = 0 ∧ q = i.succ) ∨ (p = i.succ ∧ q = 0) then 1 else 0
  c := E.c
  G := fun i r => E.G r i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
