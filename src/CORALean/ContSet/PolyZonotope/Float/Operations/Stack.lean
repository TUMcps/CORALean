module

public import CORALean.ContSet.PolyZonotope.Float.Operations.ExactPlus
public import CORALean.ContSet.PolyZonotope.Float.Operations.BlockPadLeft
public import CORALean.ContSet.PolyZonotope.Float.Operations.BlockPadRight

@[expose] public section

/-!
# `PolyZonotope.stack` over a floating-point scalar

CORA's `@polyZonotope/stack.m`, one pair (`aux_stack2`): the two sets are padded with zero blocks,
the first with `n₂` zero rows below and the second with `n₁` above, and added by `exactPlus`, so the
factors they share stay shared. The shared factor list is `hp : pZ₁.p = pZ₂.p`, as for `exactPlus`.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope

## Hypotheses
* `hp` – both have the same factor count

## Output
* polynomial zonotope of the stacked coordinates
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.stack (pZ₁ : PolyZonotope (Vec 𝕋 n₁)) (pZ₂ : PolyZonotope (Vec 𝕋 n₂))
    (hp : pZ₁.p = pZ₂.p) :
    PolyZonotope (Vec 𝕋 (n₁ + n₂)) :=
  let pZ₁t := pZ₁.blockPadLeft n₂
  let pZ₂t := pZ₂.blockPadRight n₁
  pZ₁t.exactPlus pZ₂t hp

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
