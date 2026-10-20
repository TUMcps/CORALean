module

public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_SpectraShadow
public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# An ellipsoid as a spectrahedral shadow, over a floating-point scalar

## Inputs
* `E` – ellipsoid

## Output
* Schur-form spectrahedral shadow of the ellipsoid
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The exact layer's Schur form `[[1, (x - q)ᵀ], [x - q, Q]] ⪰ 0` with the stored `Q` and `q` as
its entries and `one`, `zero` elsewhere; negation is exact, so nothing rounds. -/
def Ellipsoid.spectraShadow (E : Ellipsoid 𝕋 n) : SpectraShadow 𝕋 (Vec 𝕋 n) where
  k := n + 1
  m := n
  A₀ := fun p r =>
    Fin.cases (Fin.cases one (-E.q) r) (fun i => Fin.cases ((-E.q) i) (E.Q i) r) p
  A := fun i p r => if (p = 0 ∧ r = i.succ) ∨ (p = i.succ ∧ r = 0) then one else zero
  c := fun _ => zero
  G := fun i j => if j = i then one else zero
  I_error := E.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
