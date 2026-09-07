import CORALean.ContSet.ContSet.ContSet
import CORALean.ContSet.Zonotope.Real.Operations.Bilin

/-!
# `Zonotope.matMul`

CORA's `matZonotope * matZonotope`: `bilin` at matrix multiplication, the same
construction `mtimesMatZonotope` is at `Matrix.mulVecBilin`. `Zonotope (Mat ℝ p q)`
is CORA's `matZonotope`, so this needs no representation of its own.

The cross generators are what keeps the two factors' dependency, which is the
whole reason a power of a matrix zonotope is worth carrying instead of a power
of the interval matrix around it. Only an enclosure, though: a zonotope's
coefficients are free in `[-1, 1]` and cannot record that a cross coefficient is
a product — see `bilin`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {p q r : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.matMul (M : Zonotope (Mat ℝ p q)) (N : Zonotope (Mat ℝ q r)) :
    Zonotope (Mat ℝ p r) :=
  Zonotope.bilin matMulBilin M N

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
