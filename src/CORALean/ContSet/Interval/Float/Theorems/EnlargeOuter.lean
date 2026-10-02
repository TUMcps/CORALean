import CORALean.ContSet.Interval.Float.Operations.Enlarge
import CORALean.ContSet.Interval.Float.Theorems.CenterGe
import CORALean.ContSet.Interval.Float.Theorems.CenterLoLe
import CORALean.ContSet.Interval.Float.Theorems.RadiusOuter
import CORALean.ContSet.Interval.Real.Operations.Enlarge

/-!
# `Interval.enlarge` holds the exact layer's enlargement

For a nonnegative factor `f`, the real box `[c - f·r, c + f·r]` of the stored box's reading sits
inside the stored one: the centre is rounded away on each side, the half-width is rounded up, and a
nonnegative factor keeps the product's rounding in the outward direction. Not exact.
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

theorem Interval.enlarge_outer (I : Interval (Vec 𝕋 n)) (f : 𝕋) (hf : 0 ≤ toReal f) :
    (I.nominal.enlarge (toReal f)).construct ⊆ (I.enlarge f).construct := by -- --- PROOF ---
  intro x hx i
  have h := hx i
  have e1 : Entrywise.entry (I.nominal.enlarge (toReal f)).inf i =
      I.nominal.center i - toReal f * I.nominal.radius i := rfl
  have e2 : Entrywise.entry (I.nominal.enlarge (toReal f)).sup i =
      I.nominal.center i + toReal f * I.nominal.radius i := rfl
  rw [e1, e2] at h
  change _ ≤ x i ∧ x i ≤ _ at h
  show toReal (subDown (I.centerLo i) (mulUp f (I.radius i))) ≤ x i ∧
    x i ≤ toReal (addUp (I.center i) (mulUp f (I.radius i)))
  have hr : toReal (f) * I.nominal.radius i ≤ toReal (mulUp f (I.radius i)) :=
    le_trans (mul_le_mul_of_nonneg_left (Interval.radius_ge I i) hf) (mul_le_mulUp _ _)
  have h1 := Interval.centerLo_le I i
  have h2 := Interval.center_ge I i
  have h3 := subDown_le_sub (I.centerLo i) (mulUp f (I.radius i))
  have h4 := add_le_addUp (I.center i) (mulUp f (I.radius i))
  exact ⟨by linarith [h.1], by linarith [h.2]⟩


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
