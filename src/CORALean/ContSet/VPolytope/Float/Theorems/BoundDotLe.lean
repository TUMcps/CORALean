module

public import CORALean.ContSet.VPolytope.Float.Operations.SupportBound

@[expose] public section

/-!
# `VPolytope.boundDot` bounds the support function

No point of the set reads more than the float value, an upper bound only: the
real layer's `VPolytope.supportBound_attained` is the statement that the exact
value is reached.

## Inputs
* `P` – polytope
* `c` – linear functional
* `a` – float vector of `c`

## Hypotheses
* `hc` – `c x = ∑ aⱼ xⱼ`

## Conclusion
* `c` is at most the bound on every point of `P`
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.boundDot_le (P : VPolytope (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) :
    ∀ x ∈ P.construct, c x ≤ toReal (P.boundDot a hc).val :=
  (P.boundDot a hc).le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
