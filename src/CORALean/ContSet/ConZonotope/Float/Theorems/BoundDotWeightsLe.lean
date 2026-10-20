module

public import CORALean.ContSet.ConZonotope.Float.Operations.BoundDotWeights

@[expose] public section

/-!
# `ConZonotope.boundDotWeights` bounds the support function, at every weight vector

Whatever the weights — optimal, rounded, negative, or arbitrary — every point of
the float constrained zonotope reads at most the bound. This is the theorem that
makes the simplex untrusted: `boundDot` is this at one particular weight vector.

## Inputs
* `cZ` – float constrained zonotope
* `c` – linear functional
* `a` – float weights of the functional
* `y` – dual certificate for the inequalities
* `zu` – upper dual certificate for the equalities
* `zl` – lower dual certificate for the equalities

## Hypotheses
* `hc` – the functional is the weighted sum

## Conclusion
* every point of the set stays below the bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.boundDotWeights_le (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (a : Vec 𝕋 n) (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j)
    (y : Vec 𝕋 cZ.P.m) (zu zl : Vec 𝕋 cZ.P.me) :
    ∀ x ∈ cZ.construct, c x ≤ toReal (cZ.boundDotWeights a hc y zu zl).val :=
  (cZ.boundDotWeights a hc y zu zl).le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
