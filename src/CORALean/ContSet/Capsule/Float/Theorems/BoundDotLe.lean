module

public import CORALean.ContSet.Capsule.Float.Operations.BoundDot

@[expose] public section

/-!
# `Capsule.boundDot` bounds the capsule, in float too

## Inputs
* `C` – capsule
* `f` – linear functional
* `a` – float direction vector
* `s` – proposed norm of `a`

## Hypotheses
* `hf` – `a` represents `f`
* `hs` – `s` bounds the norm of `a`

## Conclusion
* `f` on the capsule is at most the float bound
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.boundDot_le (C : Capsule 𝕋 n) {f : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hf : ∀ x : Vec ℝ n, f x = ∑ i, toReal (a i) * x i) (s : 𝕋)
    (hs : toReal (sqSumUp fun i => absolute (a i)) ≤ toReal (mulDown s s)) :
    ∀ x ∈ C.construct, f x ≤ toReal (C.boundDot a hf s hs).val :=
  (C.boundDot a hf s hs).le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
