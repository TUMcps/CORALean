module

public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.ConZonotope.Float.Theorems.IntersectionOuter
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope

@[expose] public section

/-!
# A bundle's constrained zonotope, at one component, over a floating-point scalar
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `cZ` intersected with each member of a family in turn. -/
def ZonoBundle.interFrom (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : {k : ℕ} →
    (Fin k → Zonotope (Vec 𝕋 n)) →
    ConZonotope 𝕋 (Vec 𝕋 n)
  | 0, _ => cZ
  | _ + 1, Z => ZonoBundle.interFrom (cZ.intersection (Z 0).conZonotope) fun i => Z i.succ

def ZonoBundle.conZonotope (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) : ConZonotope 𝕋 (Vec 𝕋 n) :=
  (zB.zonotope i).conZonotope

/-- Every member at once: the first member's constrained zonotope, intersected
with each of the rest. -/
def ZonoBundle.conZonotopeAll (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k) : ConZonotope
    𝕋 (Vec 𝕋 n) :=
  ZonoBundle.interFrom (zB.conZonotope ⟨0, hk⟩)
    fun (i : Fin (zB.k - 1)) => zB.zonotope ⟨i + 1, by omega⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
