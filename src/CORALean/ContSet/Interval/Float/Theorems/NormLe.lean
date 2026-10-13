import CORALean.ContSet.Interval.Float.Theorems.NormNominalLe

/-!
# `Interval.norm` bounds every member

With a certificate `σ`, every member of the box has Euclidean norm at most `|σ|`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.norm_le (I : Interval (Vec 𝕋 n)) {σ : 𝕋}
    (hσ : toReal I.normSq ≤ toReal (mulDown σ σ)) {x : Vec ℝ n} (hx : x ∈ I.construct) :
    ‖x‖₂ ≤ toReal (absolute σ) :=
  le_trans (Real.Interval.norm_le (I := I.nominal) hx) (I.norm_nominal_le hσ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
