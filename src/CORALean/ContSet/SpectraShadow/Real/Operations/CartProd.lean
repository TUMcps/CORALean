module

public import CORALean.Global.Block
public import CORALean.ContSet.SpectraShadow.Real.Operations.Map
public import CORALean.ContSet.SpectraShadow.Real.Operations.Plus

@[expose] public section

/-!
# `SpectraShadow.cartProd`

CORA's `@spectraShadow/cartProd_`: each set is put into its own coordinates of
the product, zero in the other's, and the two are added. CORA assembles the same
set by intersecting two lifts, which needs the intersection this representation
does not compute; the sum of the two embeddings is also the block-diagonal
inequality with the centers and generators stacked, and needs only `plus`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.cartProd (S : SpectraShadow (Vec ℝ n)) (T : SpectraShadow (Vec ℝ m)) :
    SpectraShadow (Vec ℝ (n + m)) :=
  (S.map (blockPadLeft n m)).plus (T.map (blockPadRight n m))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
