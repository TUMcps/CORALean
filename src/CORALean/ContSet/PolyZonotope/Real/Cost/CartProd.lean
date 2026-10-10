import CORALean.ContSet.PolyZonotope.Real.Operations.CartProd
import CORALean.Global.Cost

/-!
# `PolyZonotope.cartProdCost`

Asserted, not proved: `Operations/CartProd.lean` pairs the centres, pads each
operand's generators with a zero in the other component and assembles the
exponent matrix block-diagonally with `plusE`, whose off-diagonal blocks are
literal zeros. Everything is placed and nothing computed.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.cartProd` costs: nothing, it only places data. -/
def PolyZonotope.cartProdCost : Cost := 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
