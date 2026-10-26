module

public import CORALean.ContSet.Interval.Float.Operations.Volume
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.ContSet.Interval.Real.Theorems.VolumeEq

@[expose] public section

/-!
# `Interval.volume` bounds the exact volume

Every width is rounded up and clipped at zero, and a product of nonnegative upper bounds, each
product rounded up, bounds the product. Read in `ENNReal`, as the exact layer's `Interval.volume`
is, so a crossed coordinate needs no case.

## Inputs
* `I` – interval box

## Hypotheses
* none

## Conclusion
* the exact volume is at most the float volume
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

private theorem aux_prod_le_prodUp : -- --- CONCL ---
    ∀ {k : ℕ} (f : Fin k → 𝕋), (∀ i, 0 ≤ toReal (f i)) →
    ∏ i, toReal (f i) ≤ toReal (prodUp f) := by -- --- PROOF ---
  intro k
  induction k with
  | zero =>
    intro f _
    rw [Finset.univ_eq_empty, Finset.prod_empty, prodUp, Fin.foldr_zero, toReal_one]
  | succ k ih =>
    -- peel the first factor: it and the rest are each bounded, the first nonnegative
    intro f hf
    have hp : prodUp f = mulUp (f 0) (prodUp fun i => f i.succ) := by
      simp only [prodUp, Fin.foldr_succ]
    rw [Fin.prod_univ_succ, hp]
    have h₁ := ih (fun i => f i.succ) (fun i => hf i.succ)
    exact le_trans (mul_le_mul_of_nonneg_left h₁ (hf 0)) (mul_le_mulUp _ _)

private theorem Interval.aux_widthUp_nonneg (I : Interval (Vec 𝕋 n)) (i : Fin n) :
    0 ≤ toReal (I.aux_widthUp i) := by
  rw [Interval.aux_widthUp, toReal_maximum, toReal_zero]
  exact le_max_left _ _

private theorem Interval.aux_widthUp_ge (I : Interval (Vec 𝕋 n)) (i : Fin n) :
    toReal (I.sup i) - toReal (I.inf i) ≤ toReal (I.aux_widthUp i) := by
  rw [Interval.aux_widthUp, toReal_maximum]
  exact le_trans (sub_le_subUp _ _) (le_max_right _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.volume_nominal_le (I : Interval (Vec 𝕋 n)) : -- --- CONCL ---
    I.nominal.volume ≤ ENNReal.ofReal (toReal I.volume) := by -- --- PROOF ---
  have hW : ∀ i, 0 ≤ toReal (I.aux_widthUp i) := I.aux_widthUp_nonneg
  calc I.nominal.volume
      ≤ ∏ i, ENNReal.ofReal (toReal (I.aux_widthUp i)) :=
        Finset.prod_le_prod' fun i _ => ENNReal.ofReal_le_ofReal (I.aux_widthUp_ge i)
    _ = ENNReal.ofReal (∏ i, toReal (I.aux_widthUp i)) :=
        (ENNReal.ofReal_prod_of_nonneg fun i _ => hW i).symm
    _ ≤ ENNReal.ofReal (toReal I.volume) :=
        ENNReal.ofReal_le_ofReal (aux_prod_le_prodUp _ hW)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
