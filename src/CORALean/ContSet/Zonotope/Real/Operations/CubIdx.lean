module

public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# The generator index of `Zonotope.cubMap`

`Fin (N₁ * N₂ * N₃)` read as the ordered triples `((k, j), c)`, lexicographically, through
`finProdFinEquiv`: the index of the `N³` generators of `Zonotope.cubMap` (one factor index per
extended column) and of the `N₃ N₂ N₁` generators of `Zonotope.cubMapMixed`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The index of the generators: `Fin (N₁ * N₂ * N₃)` read as `((k, j), c)`. -/
def Zonotope.cubIdx (N₁ N₂ N₃ : ℕ) : Fin (N₁ * N₂ * N₃) ≃ (Fin N₁ × Fin N₂) × Fin N₃ :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl _))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
