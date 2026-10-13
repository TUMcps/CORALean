import CORALean.ContSet.HPolytope.Float.Operations.DualBound

/-!
# `HPolytope.boundOfDual` bounds the support function

Weak duality: every point of the polytope reads at most the float value of any
nonnegative dual certificate the caller supplies. An upper bound only; the
certificate is not claimed optimal.
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

theorem HPolytope.boundOfDual_le (P : HPolytope 𝕋 (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (y : Vec 𝕋 P.m) (zu zl : Vec 𝕋 P.me)
    (hy : ∀ i, 0 ≤ toReal (y i)) (hzu : ∀ i, 0 ≤ toReal (zu i))
    (hzl : ∀ i, 0 ≤ toReal (zl i))
    (hc : ∀ x : Vec ℝ n, c x =
      (∑ i, toReal (y i) * (toRealMat P.A *ᵥ x) i)
        + (∑ i, toReal (zu i) * (toRealMat P.Ae *ᵥ x) i)
        - ∑ i, toReal (zl i) * (toRealMat P.Ae *ᵥ x) i) :
    ∀ x ∈ P.construct, c x ≤ toReal (P.boundOfDual y zu zl hy hzu hzl hc).val :=
  (P.boundOfDual y zu zl hy hzu hzl hc).le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
