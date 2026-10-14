module

public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_SpectraShadow
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_SpectraShadow

@[expose] public section

/-!
# A polytope as a spectrahedral shadow, over a floating-point scalar
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.spectraShadow (P : HPolytope 𝕋 (Vec 𝕋 n)) : SpectraShadow 𝕋 (Vec 𝕋 n) where
  k := P.m + (P.me + P.me)
  m := n
  -- `A₀ = diag(d)` with `d = [b; be.sup; -be.inf]`
  A₀ := fun p q => if p = q then
    Fin.append P.b (Fin.append P.be.sup fun r => neg (P.be.inf r)) p else zero
  -- `Aᵢ = diag(-C(:,i))` with `C = [A; Ae; -Ae]`
  A := fun i p q => if p = q then neg (Fin.append (fun r => P.A r i)
    (Fin.append (fun r => P.Ae r i) fun r => neg (P.Ae r i)) p) else zero
  c := fun _ => zero
  G := fun j i => if i = j then one else zero
  I_error := Interval.point fun _ => zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
