module

public import CORALean.NN.Layers.Operations.SquareChordTangentRelaxation

@[expose] public section

/-!
# The chord-tangent relaxation of the square is sound

At the stored slope `s`, which is `l + u` up to its rounding `δ`, `x² - s x` lies on the box
between `-(s/2)²` (a square is not negative) and `-l u - δ x` (the box's `(x - l)(x - u) ≤ 0`),
so its distance to `-(l u + (s/2)²) / 2` is at most `(u - l)² / 8` plus `2 Δ max(|l|, |u|) + Δ²`
for any `Δ ≥ δ`. The stored offset is the lower rounding of that middle; the error adds its
distance to the upper one, and the margin, which is not negative, only widens it.

## Inputs
* `w` – the rounding margin's factor

## Hypotheses
* `hw` – the factor is not negative

## Conclusion
* the relaxation is sound for the square
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The real band: at a slope `s` above `l + u` by at most `Δ`, `x² - s x` is within
`(u - l)² / 8 + Δ (2 k + Δ)` of `-(l u + (s/2)²) / 2` on `[l, u]`, `k` bounding `|l|` and `|u|`. -/
private theorem aux_band {l u x s Δ k : ℝ} (hl : l ≤ x) (hu : x ≤ u) (hs : l + u ≤ s)
    (hΔ : s - (l + u) ≤ Δ) (hkl : |l| ≤ k) (hku : |u| ≤ k) : -- --- CONCL ---
    |x ^ 2 - s * x + (l * u + (s / 2) ^ 2) / 2|
      ≤ (u - l) ^ 2 / 8 + Δ * (2 * k + Δ) := by -- --- PROOF ---
  -- the slope as `l + u + δ`, with `0 ≤ δ ≤ Δ`
  obtain ⟨δ, rfl⟩ : ∃ δ, s = l + u + δ := ⟨s - (l + u), by ring⟩
  have hδ : 0 ≤ δ := by linarith
  have hδΔ : δ ≤ Δ := by linarith
  have hk : 0 ≤ k := le_trans (abs_nonneg _) hkl
  have hxk : x ≤ k := le_trans hu (le_trans (le_abs_self u) hku)
  have hxk' : -k ≤ x := by linarith [neg_abs_le l]
  have hlk : -k ≤ l := by linarith [neg_abs_le l]
  have huk : u ≤ k := le_trans (le_abs_self u) hku
  have hlk' : l ≤ k := by linarith
  have huk' : -k ≤ u := by linarith
  -- the products the two sides need
  have h1 : 0 ≤ (x - l) * (u - x) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ δ * (k + x) := mul_nonneg hδ (by linarith)
  have h3 : 0 ≤ δ * (k - l) := mul_nonneg hδ (by linarith)
  have h4 : 0 ≤ δ * (k - u) := mul_nonneg hδ (by linarith)
  have h5 : 0 ≤ δ * (k + l) := mul_nonneg hδ (by linarith)
  have h6 : 0 ≤ δ * (k + u) := mul_nonneg hδ (by linarith)
  have h7 : 0 ≤ (Δ - δ) * k := mul_nonneg (by linarith) hk
  have h8 : 0 ≤ (Δ - δ) * (Δ + δ) := mul_nonneg (by linarith) (by linarith)
  have h9 : 0 ≤ δ * δ := mul_nonneg hδ hδ
  have h10 : 0 ≤ (x - (l + u + δ) / 2) ^ 2 := sq_nonneg _
  rw [abs_le]
  constructor <;> nlinarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem squareChordTangentRelaxation_encloses {w : 𝕋} (hw : 0 ≤ toReal w) : -- --- CONCL ---
    (squareChordTangentRelaxation w).Encloses (fun x => x ^ 2) := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  -- the parts of the error, named
  set sp := subUp (addUp l u) (addDown l u) with hsp
  set k := maximum (absolute l) (absolute u) with hkdef
  set R := mulUp (mulUp (subUp u l) (subUp u l)) (half (half (half (one : 𝕋)))) with hRdef
  set B := mulUp (maximum (mulUp l l) (mulUp u u)) w with hBdef
  set SC := mulUp sp (addUp (addUp k k) sp) with hSCdef
  set OC := subUp (half (neg (step_squareChordSumDown l u)))
    (half (neg (step_squareChordSumUp l u))) with hOCdef
  -- the slope between its two roundings, the middle of the box exact
  have hsU := add_le_addUp l u
  have hsD := addDown_le_add l u
  have hspread : toReal (addUp l u) - toReal (addDown l u) ≤ toReal sp := sub_le_subUp _ _
  have hm : toReal (half (addUp l u)) = toReal (addUp l u) / 2 := toReal_half _
  -- `l u + m²` between its two roundings
  have hPu : toReal l * toReal u + (toReal (addUp l u) / 2) ^ 2
      ≤ toReal (step_squareChordSumUp l u) := by
    unfold step_squareChordSumUp
    have := add_le_addUp (mulUp l u) (mulUp (half (addUp l u)) (half (addUp l u)))
    have := mul_le_mulUp l u
    have := mul_le_mulUp (half (addUp l u)) (half (addUp l u))
    rw [hm] at *
    rw [pow_two]; linarith
  have hPd : toReal (step_squareChordSumDown l u)
      ≤ toReal l * toReal u + (toReal (addUp l u) / 2) ^ 2 := by
    unfold step_squareChordSumDown
    have := addDown_le_add (mulDown l u) (mulDown (half (addUp l u)) (half (addUp l u)))
    have := mulDown_le_mul l u
    have := mulDown_le_mul (half (addUp l u)) (half (addUp l u))
    rw [hm] at *
    rw [pow_two]; linarith
  -- the radius: the width rounded up, squared and halved three times
  have hd := sub_le_subUp u l
  have hdd := mul_le_mulUp (subUp u l) (subUp u l)
  have h8 : toReal (half (half (half (one : 𝕋)))) = 1 / 8 := by
    rw [toReal_half, toReal_half, toReal_half, toReal_one]; norm_num
  have hR : toReal (mulUp (subUp u l) (subUp u l)) * (1 / 8) ≤ toReal R := by
    rw [← h8]; exact mul_le_mulUp _ _
  have hwidth : (toReal u - toReal l) ^ 2 ≤ toReal (subUp u l) * toReal (subUp u l) := by
    rw [pow_two]; exact mul_self_le_mul_self (by linarith) hd
  -- the margin is not negative
  have hll := mul_le_mulUp l l
  have hbig : 0 ≤ toReal (maximum (mulUp l l) (mulUp u u)) := by
    rw [toReal_maximum]; exact le_trans (le_trans (mul_self_nonneg _) hll) (le_max_left _ _)
  have hB0 : 0 ≤ toReal B := le_trans (mul_nonneg hbig hw) (mul_le_mulUp _ _)
  -- the slope's cost: the spread times twice the largest end plus the spread
  have hk : toReal k = max |toReal l| |toReal u| := by
    rw [hkdef, toReal_maximum, toReal_absolute, toReal_absolute]
  have hK0 : 0 ≤ toReal k := hk ▸ le_trans (abs_nonneg _) (le_max_left _ _)
  have hkk := add_le_addUp k k
  have hinner := add_le_addUp (addUp k k) sp
  have hslope : toReal sp * (2 * toReal k + toReal sp) ≤ toReal SC :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) (mul_le_mulUp _ _)
  -- the offset's cost: the distance between the two roundings of the middle
  have hO := sub_le_subUp (half (neg (step_squareChordSumDown l u)))
    (half (neg (step_squareChordSumUp l u)))
  rw [toReal_half, toReal_half, toReal_neg, toReal_neg] at hO
  -- the real band at the stored slope
  have hband := aux_band (s := toReal (addUp l u)) (Δ := toReal sp) (k := toReal k) hl hu
    (by linarith) (by linarith) (hk ▸ le_max_left _ _) (hk ▸ le_max_right _ _)
  -- the stored error is at least the sum of its parts
  have he := add_le_addUp (addUp (addUp R B) SC) OC
  have he2 := add_le_addUp (addUp R B) SC
  have he3 := add_le_addUp R B
  show |t ^ 2 - (toReal (addUp l u) * t + toReal (half (neg (step_squareChordSumUp l u))))|
    ≤ toReal (addUp (addUp (addUp R B) SC) OC)
  rw [toReal_half, toReal_neg]
  rw [abs_le] at hband ⊢
  constructor <;> linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
