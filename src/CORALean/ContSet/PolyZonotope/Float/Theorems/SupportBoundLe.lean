import CORALean.ContSet.PolyZonotope.Float.Operations.SupportBound

/-!
# `PolyZonotope.supportBound` bounds the set, in float too
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

theorem PolyZonotope.supportBound_le (pZ : PolyZonotope (Vec 𝕋 n))
    {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j)
    (u : FloatBound 𝕋 ((InflatedContSet.nominal pZ).subsetAt {a | ∀ k, |a k| ≤ 1}) c) :
    ∀ x ∈ pZ.construct, c x ≤ toReal (pZ.supportBound a hc u).val :=
  (pZ.supportBound a hc u).le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
