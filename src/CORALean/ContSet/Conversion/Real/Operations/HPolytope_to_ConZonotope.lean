module

public import CORALean.ContSet.Conversion.Real.HPolytope_to_Zonotope
public import CORALean.ContSet.Zonotope.Real.Operations.GenMap
public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.HPolytope.Real.Theorems.TranslateExact
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic

@[expose] public section

/-!
# A halfspace description as a constrained zonotope — the construction

`HPolytope.conZonotope` is the construction; `HPolytope_to_ConZonotope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def HPolytope.conZonotope
    (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : ConZonotope (Vec ℝ n) where
  h := (HPolytope.zonotope up lo).h
  c := (HPolytope.zonotope up lo).c
  G := (HPolytope.zonotope up lo).G
  P := (P.translate (-(HPolytope.zonotope up lo).c)).comap (HPolytope.zonotope up lo).genMap

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
