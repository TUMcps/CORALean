module

public import CORALean.ContSet.Taylm.Float.Operations.Scale
public import CORALean.ContSet.Taylm.Float.Theorems.AbsorbRoundingNominal
public import CORALean.ContSet.Taylm.Float.Theorems.AbsPolyOfRoundLe
public import CORALean.ContSet.Taylm.Float.Theorems.TimesZeroInfMem
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfSmul

@[expose] public section

/-!
# `Taylm.scale` encloses the product with the number

## Inputs
* `T` – Taylor model
* `f` – enclosed function
* `s` – number

## Hypotheses
* `h` – `T` encloses `f`

## Conclusion
* the scaled model encloses `f · s`
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.scale_outer {T : Taylm 𝕋 n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (s : 𝕋) : -- --- CONCL ---
    (T.scale s).Encloses fun t => f t * toReal s := by -- --- PROOF ---
  intro t ht
  -- the remainder with the box in it, times the number
  have hr := Taylm.absorbRounding_nominal h t ht
  simp only [Taylm.nominal, Taylm.absorbRounding, Real.Taylm.poly] at hr
  have hm := Taylm.timesZeroInf_mem (a := T.absorbRounding.rem) (b := ⟨s, s⟩) hr.1 hr.2
    (le_refl (toReal s)) le_rfl
  -- the exact scaled coefficients against the stored upper roundings
  have hround := Taylm.abs_polyOf_round_le T.terms (fun a => mulDown a.1 s)
    (fun a => mulUp a.1 s) (fun a => toReal s * toReal a.1) (fun a => a.2)
    (fun a _ => ⟨by rw [mul_comm]; exact mulDown_le_mul _ _,
      by rw [mul_comm]; exact mul_le_mulUp _ _⟩) ht
  have hex : Real.Taylm.polyOf (T.terms.map fun a => (toReal s * toReal a.1, a.2)) t
      = toReal s * Real.Taylm.polyOf (T.terms.map fun a => (toReal a.1, a.2)) t := by
    rw [← Real.Taylm.polyOf_smul, List.map_map]
    rfl
  rw [hex] at hround
  have hb := abs_le.1 hround
  set P := Real.Taylm.polyOf (T.terms.map fun a => (toReal a.1, a.2)) t
  have e : f t * toReal s = (f t - P) * toReal s + toReal s * P := by ring
  simp only [Taylm.scale, Taylm.inflated, Real.Taylm.poly, List.map_map, Taylm.absorbRounding,
    toReal_neg] at *
  simp only [Function.comp_def] at *
  rw [e]
  constructor <;> linarith [hm.1, hm.2, hb.1, hb.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
