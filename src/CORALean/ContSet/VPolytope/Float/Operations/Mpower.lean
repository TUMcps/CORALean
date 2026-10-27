module

public import CORALean.ContSet.VPolytope.Float.Operations.MatMul

@[expose] public section

/-!
# `VPolytope.mpower`, over a floating-point scalar

CORA's `mpower` of a matrix polytope, rounded outward: the identity for the exponent `0`, the
polytope itself for `1`, and then `((P * P) * P) * …`, each product `VPolytope.matMul` with the
running power on the left, as CORA's loop multiplies.

## Inputs
* `P` – matrix polytope

## Output
* matrix polytope enclosing the `k`-th power of its members
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The identity, `P`, then the running power times `P` from the right. -/
def VPolytope.mpower (P : VPolytope (Mat 𝕋 n n)) : ℕ → VPolytope (Mat 𝕋 n n)
  | 0 => ⟨1, fun _ => diagonalBlock fun _ => one, Interval.point fun _ _ => zero⟩
  | 1 => P
  | k + 2 => VPolytope.matMul (VPolytope.mpower P (k + 1)) P

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
