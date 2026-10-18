module

public import CORALean.ContSet.ZonoBundle.Float.Theorems.ConstructEqIInter
public import CORALean.ContSet.ZonoBundle.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.OriginExact

@[expose] public section

/-!
# `ZonoBundle.origin` is exactly the origin

A one-member intersection is that member, which `Zonotope.origin_exact` says is `{0}`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.origin_exact (n : ℕ) :
    (ZonoBundle.origin n : ZonoBundle (Vec 𝕋 n)).construct = {0} := by
  rw [ZonoBundle.construct_eq_iInter]
  show ⋂ _ : Fin 1, (Zonotope.origin n : Zonotope (Vec 𝕋 n)).construct = {0}
  rw [Set.iInter_const]
  exact Zonotope.origin_exact n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
