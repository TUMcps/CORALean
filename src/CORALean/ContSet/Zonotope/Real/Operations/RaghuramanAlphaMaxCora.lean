module

public import CORALean.ContSet.Zonotope.Real.Operations.RaghuramanGProdCora

@[expose] public section

/-!
# `Zonotope.raghuramanAlphaMaxCora`, CORA's `alpha_max` in the `'raghuraman'` reduction

`[alpha_max,idx] = max(abs(G_prod),[],2)` (lines 271-272 of `@zonotope/reduceUnderApprox.m`): the
largest absolute alignment of each small generator with a kept one. Line 276 then divides
`G_prod(k, idx)` by it; at `alpha_max = 0` that is `0/0`, which MATLAB evaluates to `NaN`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `alpha_max`, one entry per small generator. -/
noncomputable def Zonotope.raghuramanAlphaMaxCora (Z : Zonotope (Vec ℝ n)) (etaNew : ℕ)
    (hr : etaNew ≤ Z.h) : Fin (Z.h - etaNew) → ℝ :=
  let G_prod := Z.raghuramanGProdCora etaNew hr           -- G_prod = G_small'*G_big
  let alphas := fun k i => |G_prod k i|                   -- alphas = abs(G_prod)
  fun k => ⨆ i, alphas k i                                -- [alpha_max,idx] = max(alphas,[],2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
