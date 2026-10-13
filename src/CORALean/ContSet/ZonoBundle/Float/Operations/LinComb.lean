module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.Zonotope.Float.Operations.LinComb

@[expose] public section

/-!
# `ZonoBundle.linComb`

Every pair of members combined by `Zonotope.linComb` and indexed through
`finProdFinEquiv`, exactly as `plus` sums pairs.

Computable, unlike the exact layer's, which is `noncomputable` only because
`Zonotope.linComb` halves a centre in ℝ. The interpolation weight is still
shared across every pair — only the endpoints vary — which is what
`Theorems.LinCombOuter` turns into the enclosure.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.linComb (zB₁ zB₂ : ZonoBundle (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) where
  k := zB₁.k * zB₂.k
  Z := fun p =>
    Zonotope.linComb (zB₁.Z (finProdFinEquiv.symm p).1) (zB₂.Z (finProdFinEquiv.symm p).2)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
