module

public import CORALean.ContSet.ConPolyZono.Float.Operations.SupportBound

@[expose] public section

/-!
# The float support bound of a constrained polynomial zonotope is an upper bound

No point of the set exceeds `supportBound` in the direction `a`: the dependent part's argument
bound, the independent block's rounded extent and the error box's, each rounded upward. An
upper bound only, as over ℝ; equality with CORA's value is not claimed.
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

theorem ConPolyZono.supportBound_le (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (a : Vec 𝕋 n) (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j)
    (u : FloatBound 𝕋 ((InflatedContSet.nominal cPZ).polyZonotope.point ''
      {α | (∀ k, |α k| ≤ 1) ∧ (InflatedContSet.nominal cPZ).satisfies α}) c) :
    ∀ x ∈ cPZ.construct, c x ≤ toReal (cPZ.supportBound a hc u).val :=
  (cPZ.supportBound a hc u).le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
