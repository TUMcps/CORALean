module

public import CORALean.NN.Layers.Operations.RelaxationOfAffineConj
public import CORALean.NN.Layers.Theorems.AbsSubLeSpread

@[expose] public section

/-!
# A relaxation carried along an affine conjugation is sound

`g t = ra f (rb t) + c` inherits `f`'s soundness: its deviation from the exactly scaled affine
map is `ra` times `f`'s, and what storing one slope and one offset costs on top is bounded by the
two gaps — the slope's charged against `|t|`, which only the box bounds. The two scales arrive
here, as hypotheses on the roundings, and nowhere in what is stored.

## Inputs
* `R` – relaxation of the activation
* `A` – rounding of the output scale
* `B` – rounding of the input scale
* `c` – output shift

## Hypotheses
* `hR` – relaxation is sound for the activation
* `hA` – output rounding is sound for its scale
* `hB` – input rounding is sound for its scale
* `ha` – output scale is positive
* `hb` – input scale is positive
* `hg` – the conjugate is the scaled activation plus the shift

## Conclusion
* the conjugated relaxation is sound for the conjugate
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {f g : ℝ → ℝ} {ra rb : ℝ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- `ra ≥ 0` is what lets the outer rounding preserve the inner one's direction
theorem aux_conjSlopeLow_le (R : Relaxation 𝕋) {A B : ScaleRounding 𝕋}
    (hA : A.Sound ra) (hB : B.Sound rb) (ha : 0 ≤ ra) (l u : 𝕋) : -- --- CONCL ---
    toReal (Relaxation.conjSlopeLow R A B l u)
      ≤ ra * rb * toReal (R.slope (B.down l) (B.up u)) := by -- --- PROOF ---
  rw [Relaxation.conjSlopeLow]
  calc toReal (A.down (B.down (R.slope (B.down l) (B.up u))))
      ≤ ra * toReal (B.down (R.slope (B.down l) (B.up u))) :=
        hA.down_le (B.down (R.slope (B.down l) (B.up u)))
    _ ≤ ra * (rb * toReal (R.slope (B.down l) (B.up u))) :=
        mul_le_mul_of_nonneg_left (hB.down_le (R.slope (B.down l) (B.up u))) ha
    _ = ra * rb * toReal (R.slope (B.down l) (B.up u)) := by ring

theorem aux_le_conjSlopeHigh (R : Relaxation 𝕋) {A B : ScaleRounding 𝕋}
    (hA : A.Sound ra) (hB : B.Sound rb) (ha : 0 ≤ ra) (l u : 𝕋) : -- --- CONCL ---
    ra * rb * toReal (R.slope (B.down l) (B.up u))
      ≤ toReal (Relaxation.conjSlopeHigh R A B l u) := by -- --- PROOF ---
  rw [Relaxation.conjSlopeHigh]
  calc ra * rb * toReal (R.slope (B.down l) (B.up u))
      = ra * (rb * toReal (R.slope (B.down l) (B.up u))) := by ring
    _ ≤ ra * toReal (B.up (R.slope (B.down l) (B.up u))) :=
        mul_le_mul_of_nonneg_left (hB.up_ge (R.slope (B.down l) (B.up u))) ha
    _ ≤ toReal (A.up (B.up (R.slope (B.down l) (B.up u)))) :=
        hA.up_ge (B.up (R.slope (B.down l) (B.up u)))

theorem aux_conjOffsetLow_le (R : Relaxation 𝕋) {A : ScaleRounding 𝕋}
    (hA : A.Sound ra) (B : ScaleRounding 𝕋) (c l u : 𝕋) :
    toReal (Relaxation.conjOffsetLow R A B c l u)
      ≤ ra * toReal (R.offset (B.down l) (B.up u)) + toReal c := by
  rw [Relaxation.conjOffsetLow]
  have h1 := hA.down_le (R.offset (B.down l) (B.up u))
  have h2 := addDown_le_add (A.down (R.offset (B.down l) (B.up u))) c
  linarith

-- the mirrored bound, no sign hypothesis needed here either
theorem aux_le_conjOffsetHigh (R : Relaxation 𝕋) {A : ScaleRounding 𝕋}
    (hA : A.Sound ra) (B : ScaleRounding 𝕋) (c l u : 𝕋) :
    ra * toReal (R.offset (B.down l) (B.up u)) + toReal c
      ≤ toReal (Relaxation.conjOffsetHigh R A B c l u) := by
  rw [Relaxation.conjOffsetHigh]
  have h1 := hA.up_ge (R.offset (B.down l) (B.up u))
  have h2 := add_le_addUp (A.up (R.offset (B.down l) (B.up u))) c
  linarith

theorem aux_abs_le_conjTBound {l u : 𝕋} {t : ℝ} (hl : toReal l ≤ t)
    (hu : t ≤ toReal u) : -- --- CONCL ---
    |t| ≤ toReal (Relaxation.conjTBound l u) := by -- --- PROOF ---
  rw [Relaxation.conjTBound, toReal_maximum, toReal_absolute, toReal_absolute, abs_le]
  have hnl : -toReal l ≤ |toReal l| := by rw [← abs_neg]; exact le_abs_self _
  have hnu : toReal u ≤ |toReal u| := le_abs_self _
  refine ⟨?_, ?_⟩
  · have := le_max_left |toReal l| |toReal u|
    linarith
  · have := le_max_right |toReal l| |toReal u|
    linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- `g t = ra f (rb t) + c` inherits `f`'s soundness, and this is where the two real scales
arrive: `ofAffineConj` itself stores only scalars. -/
theorem Relaxation.ofAffineConj_sound {R : Relaxation 𝕋} {A B : ScaleRounding 𝕋} {c : 𝕋}
    (hR : R.Sound f) (hA : A.Sound ra) (hB : B.Sound rb) (ha : 0 < ra) (hb : 0 < rb)
    (hg : ∀ t, g t = ra * f (rb * t) + toReal c) : -- --- CONCL ---
    (Relaxation.ofAffineConj R A B c).Sound g := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  show |g t - (toReal (Relaxation.conjSlope R A B l u) * t
    + toReal (Relaxation.conjOffset R A B c l u))| ≤ toReal (Relaxation.conjError R A B c l u)
  have hbl : toReal (B.down l) ≤ rb * t :=
    le_trans (hB.down_le l) (mul_le_mul_of_nonneg_left hl hb.le)
  have hbu : rb * t ≤ toReal (B.up u) :=
    le_trans (mul_le_mul_of_nonneg_left hu hb.le) (hB.up_ge u)
  have hRsound := hR.sound hbl hbu
  set sl := toReal (R.slope (B.down l) (B.up u)) with hsl
  set off := toReal (R.offset (B.down l) (B.up u)) with hoff
  -- the affine map's own slope and offset cancel, leaving `ra` times `f`'s deviation
  have heq : g t - (ra * rb * sl * t
        + (ra * off + toReal c))
      = ra * (f (rb * t) - (sl * (rb * t)
        + off)) := by
    rw [hg t]; ring
  have hbound1 : |g t - (ra * rb * sl * t
        + (ra * off + toReal c))|
      ≤ ra * toReal (R.error (B.down l) (B.up u)) := by
    rw [heq, abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left hRsound ha.le
  have hSlopeLow := aux_conjSlopeLow_le R hA hB ha.le l u
  have hSlopeHigh := aux_le_conjSlopeHigh R hA hB ha.le l u
  have hOffsetLow := aux_conjOffsetLow_le R hA B c l u
  have hOffsetHigh := aux_le_conjOffsetHigh R hA B c l u
  -- how far the chosen slope and offset can be from the exact product and sum
  have hSlopeGap : |ra * rb * sl
        - toReal (Relaxation.conjSlope R A B l u)|
      ≤ toReal (Relaxation.conjSlopeGap R A B l u) := by
    rw [Relaxation.conjSlopeGap]; exact abs_sub_le_spread hSlopeLow hSlopeHigh
  have hOffsetGap : |(ra * off + toReal c)
        - toReal (Relaxation.conjOffset R A B c l u)|
      ≤ toReal (Relaxation.conjOffsetGap R A B c l u) := by
    rw [Relaxation.conjOffsetGap]; exact abs_sub_le_spread hOffsetLow hOffsetHigh
  have htBound := aux_abs_le_conjTBound hl hu
  -- the rounded slope gap against the box bound of `t`
  set gt := mulUp (Relaxation.conjSlopeGap R A B l u) (Relaxation.conjTBound l u) with hgt
  -- the slope gap multiplies `t`, bounded only by the box, not by anything smaller
  have hcorrection : |(ra * rb * sl
        - toReal (Relaxation.conjSlope R A B l u)) * t|
      ≤ toReal gt := by
    rw [abs_mul]
    have hnn : (0:ℝ) ≤ toReal (Relaxation.conjSlopeGap R A B l u) :=
      le_trans (abs_nonneg _) hSlopeGap
    exact le_trans (mul_le_mul hSlopeGap htBound (abs_nonneg t) hnn) (mul_le_mulUp _ _)
  -- the goal splits into the three pieces just bounded, plus their own roundings
  have hkey : g t - (toReal (Relaxation.conjSlope R A B l u) * t
        + toReal (Relaxation.conjOffset R A B c l u))
      = (g t - (ra * rb * sl * t
          + (ra * off + toReal c)))
        + (ra * rb * sl
          - toReal (Relaxation.conjSlope R A B l u)) * t
        + ((ra * off + toReal c)
          - toReal (Relaxation.conjOffset R A B c l u)) := by
    ring
  rw [hkey]
  have htri1 := abs_add_le (g t - (ra * rb * sl * t
      + (ra * off + toReal c))
    + (ra * rb * sl
      - toReal (Relaxation.conjSlope R A B l u)) * t)
    ((ra * off + toReal c)
      - toReal (Relaxation.conjOffset R A B c l u))
  -- the same split, one level in: the first two pieces against each other
  have htri2 := abs_add_le (g t - (ra * rb * sl * t
      + (ra * off + toReal c)))
    ((ra * rb * sl
      - toReal (Relaxation.conjSlope R A B l u)) * t)
  have hstep1 := add_le_addUp (A.up (R.error (B.down l) (B.up u))) gt
  have hstep2 := add_le_addUp (addUp (A.up (R.error (B.down l) (B.up u))) gt)
    (Relaxation.conjOffsetGap R A B c l u)
  have hErrRound := hA.up_ge (R.error (B.down l) (B.up u))
  rw [Relaxation.conjError]
  linarith [hbound1, hcorrection, hOffsetGap, htri1, htri2, hstep1, hstep2, hErrRound]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
