module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle

@[expose] public section

/-!
# `ZonoBundle.intersection`

CORA's `zonoBundle`/`and` at float zonotopes: appending the two families, as
over ℝ. No arithmetic runs, so nothing rounds and each member keeps the error
box it arrived with — which is why this stays *exact* in the float layer too,
per `Theorems.AndExact`.

## Inputs
* `zB₁` – first bundle
* `zB₂` – second bundle

## Output
* the intersection of the two bundles
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.intersection (zB₁ zB₂ : ZonoBundle (Vec 𝕋 n)) : ZonoBundle (Vec 𝕋 n) where
  k := zB₁.k + zB₂.k
  Z := Fin.append zB₁.Z zB₂.Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
