module

public import CORALean.ContSet.HPolytope.Float.Operations.DualBound

@[expose] public section

/-!
# `HPolytope.boundOfDual` bounds the support function

Weak duality: every point of the polytope reads at most the float value of any
nonnegative dual certificate the caller supplies. An upper bound only; the
certificate is not claimed optimal.

## Inputs
* `P` – H-polytope
* `c` – center of length `n →ₗ[ℝ] ℝ`
* `y` – vector of length `P.m`
* `zu` – vector of length `P.me`
* `zl` – vector of length `P.me`

## Hypotheses
* `hy` – the entries of `y` are nonnegative
* `hzu` – the entries of `zu` are nonnegative
* `hzl` – the entries of `zl` are nonnegative
* `hc` – `c` is the dual combination of the rows with weights `y`, `zu`, `zl`

## Conclusion
* `HPolytope.boundOfDual` bounds the support function
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
        - ∑ i, toReal (zl i) * (toRealMat P.Ae *ᵥ x) i) : -- --- CONCL ---
    ∀ x ∈ P.construct, c x ≤ toReal (P.boundOfDual y zu zl hy hzu hzl hc).val :=
  (P.boundOfDual y zu zl hy hzu hzl hc).le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
