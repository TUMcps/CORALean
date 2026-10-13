import CORALean.ContSet.ZonoBundle.Float.Operations.QuadMap
import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapOuter

/-!
# `ZonoBundle.quadMap` over-approximates the quadratic map, over a floating-point scalar

A point of the intersection lies in every member, so its image lies in every member's
`Zonotope.quadMap_outer`, hence in their intersection.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.quadMap_outer (Q : Fin m → Mat 𝕋 n n) (zB : ZonoBundle (Vec 𝕋 n)) :
    Real.PolyZonotope.quadEval (fun k => toRealMat (Q k)) '' zB.construct
      ⊆ (zB.quadMap Q).construct := by
  rintro _ ⟨x, hx, rfl⟩
  simp only [ZonoBundle.construct, Set.mem_iInter] at hx ⊢
  exact fun i => Zonotope.quadMap_outer Q (zB.Z i) ⟨x, hx i, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
