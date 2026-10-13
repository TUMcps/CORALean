import CORALean.ContSet.PolyZonotope.Real.Operations.ExactPlus
import CORALean.ContSet.PolyZonotope.Real.Operations.Map
import CORALean.Global.Block

/-!
# `PolyZonotope.stack`

CORA's `@polyZonotope/stack.m`, one pair (`aux_stack2`): the two sets are padded with zero
blocks, `pZ1t` with `n2` zero rows below and `pZ2t` with `n1` above, and added by `exactPlus`,
so the factors they share stay shared. The padding is `PolyZonotope.map` at the two block
embeddings. The shared factor list is `hp : pZ₁.p = pZ₂.p`, as for `exactPlus`; CORA's empty-set
and empty-generator cases return the other padded set, which `exactPlus` already is.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n₁ n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The stack of two sets over one factor list: `exactPlus` of the zero-padded pair. -/
def PolyZonotope.stack (pZ₁ : PolyZonotope (Vec ℝ n₁)) (pZ₂ : PolyZonotope (Vec ℝ n₂))
    (hp : pZ₁.p = pZ₂.p) : PolyZonotope (Vec ℝ (n₁ + n₂)) :=
  let pZ₁t := pZ₁.map (blockPadLeft n₁ n₂)
  let pZ₂t := pZ₂.map (blockPadRight n₁ n₂)
  pZ₁t.exactPlus pZ₂t hp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
