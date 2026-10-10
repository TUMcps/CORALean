import CORALean.ContSet.ConZonotope.Float.Operations.BoundDotWeights
import CORALean.ContSet.HPolytope.Float.Operations.DualWeights

/-!
# `ConZonotope.boundDot`: a float constrained zonotope answers a direction

`boundDotWeights` at the weights `HPolytope.dualWeights` proposes for `Gᵀa`, the
exact simplex at ℚ on the floats' own values. With all weights zero (the budget
ran out) this is the zonotope bound `aᵀc + Σⱼ |aᵀGⱼ|`, the constraints ignored;
with the simplex's optimal weights it is the program's value up to rounding.
Either way an upper bound only, never claimed to be the support function.

CORA's `supportFunc_` of a `conZonotope` solves the same program with `linprog`
and returns its value: this is that, read as a bound.

A NaN among the stored data reads through `ToRat` as `1.5 · 2 ^ 1024`, so the program solved
is another one. That costs tightness only: the checker sees the NaN in rounded arithmetic.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bound at the weights the exact simplex proposes for `Gᵀa`, computed in ℚ
from the floats' own values. Checked, not trusted. -/
def ConZonotope.boundDot [ToRat 𝕋] (cZ : ConZonotope 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (a : Vec 𝕋 n) (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) :
    FloatBound 𝕋 cZ.construct c :=
  let w := cZ.P.dualWeights fun j => ∑ i, ToRat.toRat (a i) * ToRat.toRat (cZ.G j i)
  cZ.boundDotWeights a hc w.1 w.2.1 w.2.2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
