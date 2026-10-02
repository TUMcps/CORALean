import CORALean.ContSet.Interval.Float.Operations.RadiusSq
import CORALean.ContSet.Interval.Float.Theorems.RadiusOuter
import CORALean.ContSet.Interval.Real.Operations.Radius2

/-!
# `Interval.radiusSq` bounds the exact `radius₂`

The stored half-widths bound the exact ones for a nonempty box, so a certificate `σ` with
`radiusSq ≤ σ·σ` bounds the exact layer's `Interval.radius₂` by `|σ|`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.radius₂_nominal_le (I : Interval (Vec 𝕋 n))
    (hI : ∀ i, toReal (I.inf i) ≤ toReal (I.sup i)) {σ : 𝕋}
    (hσ : toReal I.radiusSq ≤ toReal (mulDown σ σ)) :
    I.nominal.radius₂ ≤ toReal (absolute σ) := by -- --- PROOF ---
  refine norm₂_le_of_sq_le (m := I.radius) (fun i => ?_) hσ
  have h0 : 0 ≤ I.nominal.radius i := by
    show 0 ≤ (2:ℝ)⁻¹ * (toReal (I.sup i) - toReal (I.inf i))
    linarith [hI i]
  rw [abs_of_nonneg h0]
  exact I.radius_ge i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
