module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
public import CORALean.ContSet.Zonotope.Float.Operations.LinComb

@[expose] public section

/-!
# `ZonoBundle.encloseCora`

CORA's `zonoBundle`/`enclose(zB, zB2)` for two bundles of the same number of members: member `i`
of the result encloses member `i` of both, `Zonotope.linComb`. `ZonoBundle.linComb` combines
every pair of members instead (`k₁ k₂` of them), which is a tighter bundle, not CORA's.

## Inputs
* `zB₁` – first bundle
* `zB₂` – second bundle, as many members as the first

## Hypotheses
* `h` – the member counts agree

## Output
* bundle that encloses the convex hull of the union
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       22-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.encloseCora (zB₁ zB₂ : ZonoBundle (Vec 𝕋 n)) (h : zB₂.k = zB₁.k) :
    ZonoBundle (Vec 𝕋 n) where
  k := zB₁.k
  Z := fun i => Zonotope.linComb (zB₁.Z i) (zB₂.Z (Fin.cast h.symm i))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
