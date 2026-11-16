module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Basic

@[expose] public section

/-!
# `PolyZonotope.powerExt`

The terms of the power `x^i` of a row, in the layout CORA's `evaluatePolyZonotopeNeuron` keeps
them: `x^i` is the product of `x^(i/2)` and `x^((i+1)/2)`, and it keeps the terms of both factors
(scaled, so in the same order) and then the new products, the squares and the pairs of a power
with itself, every pair otherwise. Over exponent columns with `+` this is CORA's exponent matrix
of the power, over monomial values with `*` the values of its monomials.

## Inputs
* `f` – product of two terms
* `M` – terms of the first power
* `i` – exponent of the power

## Output
* terms of the power `i`, those of its factors first
-/

-- Authors:       Claude Opus 5.5
-- Written:       16-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {β : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.powerExt (f : β → β → β) (M : List β) (i : ℕ) : List β :=
  if i < 2 then M else
    if i % 2 = 0 then
      -- a square: both factors, the squares, the pairs
      PolyZonotope.powerExt f M (i / 2) ++ PolyZonotope.powerExt f M (i / 2)
        ++ (PolyZonotope.powerExt f M (i / 2)).map (fun a => f a a)
        ++ PolyZonotope.pairsWith f (PolyZonotope.powerExt f M (i / 2))
    else
      -- two different factors: both, and every product
      PolyZonotope.powerExt f M (i / 2) ++ PolyZonotope.powerExt f M ((i + 1) / 2)
        ++ PolyZonotope.crossWith f (PolyZonotope.powerExt f M (i / 2))
          (PolyZonotope.powerExt f M ((i + 1) / 2))
termination_by i
decreasing_by all_goals omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
