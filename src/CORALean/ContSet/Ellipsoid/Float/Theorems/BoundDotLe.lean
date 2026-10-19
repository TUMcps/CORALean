module

public import CORALean.ContSet.Ellipsoid.Float.Operations.SupportBound

@[expose] public section

/-!
# `Ellipsoid.boundDot` bounds the support function

No point of the set reads more than the float value, an upper bound only: the
real layer's `Ellipsoid.supportBound_attained` is the statement that the exact
value is reached.

## Inputs
* `E` – ellipsoid
* `c` – linear functional
* `a` – float vector of `c`
* `s` – length bounding `√(aᵀ Q a)`

## Hypotheses
* `hc` – `c x = ∑ aᵢ xᵢ`
* `hs` – `aᵀ Q a ≤ s²`

## Conclusion
* `c` is at most the bound on every point of `E`
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.boundDot_le (E : Ellipsoid 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) (s : 𝕋)
    (hs : toReal (E.quadUp a) ≤ toReal (mulDown s s)) :
    ∀ x ∈ E.construct, c x ≤ toReal (E.boundDot a hc s hs).val :=
  (E.boundDot a hc s hs).le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
