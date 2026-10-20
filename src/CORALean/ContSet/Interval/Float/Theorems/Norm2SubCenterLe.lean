module

public import CORALean.ContSet.Interval.Float.Theorems.Radius2NominalLe
public import CORALean.ContSet.Interval.Real.Theorems.NormSubCenterLe

@[expose] public section

/-!
# A member is within the certified bound of the center

In `‖·‖₂`, from the certificate of `Radius2NominalLe`; a member forces the box nonempty.

## Inputs
* `I` – interval box
* `σ` – certified bound of the radius
* `x` – real point

## Hypotheses
* `hσ` – squared radius at most `σ` squared
* `hx` – `x` lies in `I`

## Conclusion
* the distance of `x` to the center is at most the certified bound
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

theorem Interval.norm₂_sub_center_le (I : Interval (Vec 𝕋 n)) {σ : 𝕋}
    (hσ : toReal I.radiusSq ≤ toReal (mulDown σ σ)) {x : Vec ℝ n} (hx : x ∈ I.construct) :
    ‖x - I.nominal.center‖₂ ≤ toReal (absolute σ) :=
  le_trans (Real.Interval.norm₂_sub_center_le (I := I.nominal) hx)
    (I.radius₂_nominal_le (fun i => le_trans (hx i).1 (hx i).2) hσ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
