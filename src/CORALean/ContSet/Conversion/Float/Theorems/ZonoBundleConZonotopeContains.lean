module

public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeConZonotopeContains
public import CORALean.ContSet.ConZonotope.Float.Theorems.IntersectionOuter
public import CORALean.ContSet.Conversion.Float.Operations.ZonoBundle_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# A bundle's constrained zonotope, at one component, over a floating-point scalar

Through `ZonoBundle.zonotope i`, then the constrained zonotope with nothing to
satisfy. Whichever component `i` names, the guarantee holds.

`conZonotopeAll` keeps every member instead: the first member's constrained
zonotope intersected, one `ConZonotope.intersection` at a time, with each of the
others, which is CORA's `conZonotope(zB)` — every member's generators side by
side, tied together by agreement rows. Outer, as each intersection is, so the
whole bundle lies inside it; needs a first member, `0 < k`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.conZonotope_contains (zB : ZonoBundle (Vec 𝕋 n)) (i : Fin zB.k) :
    zB.construct ⊆ (zB.conZonotope i).construct :=
  subset_trans (zB.zonotope_contains i) (Zonotope.conZonotope_contains _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
