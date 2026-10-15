module

public import CORALean.ContSet.Zonotope.Real.Operations.MatMul
public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint

@[expose] public section

/-!
# `Zonotope.mpower`

CORA's `@matZonotope/mpower`: the zero power is the identity (center `eye`, no generators), the
first is the zonotope itself, and from the second on `matZ * matZ` is multiplied by `matZ` on the
right, once per further exponent. Only for square matrices (`eye(dim(matZ))` of a rectangular
zonotope is no identity, and the product needs a square one).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `matZ ^ k` of CORA, left to right: `((Z * Z) * Z) * …`. -/
def Zonotope.mpower (Z : Zonotope (Mat ℝ n n)) : ℕ → Zonotope (Mat ℝ n n)
  | 0 => Zonotope.ofPoint 1
  | 1 => Z
  | k + 2 => Zonotope.matMul (Zonotope.mpower Z (k + 1)) Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
