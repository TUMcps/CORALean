module

public import CORALean.NN.Layers.Operations.ReciprocalRelaxation
public import CORALean.NN.Layers.Theorems.OfBandEnclosesWhere
public import CORALean.Global.Float.SqrtDownCoraLe

@[expose] public section

/-!
# The chord relaxation of the clamped reciprocal is sound

At the stored slope `m < 0`, `g(x) = 1 / max(x, 1) - m x` is `1 - m x` up to `x = 1`, rising, and
`1/x - m x` after it, below its chord as `(x - a)(u - x) ≥ 0`: so on `[l, u]` it is at most the
largest of its values at `l`, `u` and `1` clamped into the box. Below, it is at least `g(l)` where
it rises and `2 √(-m)` after `1`, by `1/x + s² x - 2 s = (s x - 1)² / x` at `s = √(-m)`. The margin
is not negative, so `Relaxation.ofBand_enclosesWhere` concludes, on every box.

## Inputs
* `p` – the square root's Newton steps
* `w` – the margin's factor

## Hypotheses
* `hw` – the factor is not negative

## Conclusion
* the relaxation is sound for `x ↦ 1 / max(x, 1)`
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

/-- The real upper end: for `m ≤ 0`, `g` on `[l, u]` is at most its largest value at `l`, `u` and
`min(max(1, l), u)`. -/
private theorem aux_le_max {m l u t : ℝ} (hm : m ≤ 0) (hl : l ≤ t) (hu : t ≤ u) : -- --- CONCL ---
    1 / max t 1 - m * t ≤ max (max (1 / max l 1 - m * l) (1 / max u 1 - m * u))
      (1 / max (min (max 1 l) u) 1 - m * min (max 1 l) u) := by -- --- PROOF ---
  rcases le_total t 1 with ht | ht
  · -- rising: at most `g(u)` when `u ≤ 1`, else `g(1)`
    rw [max_eq_right ht]
    rcases le_total u 1 with hu1 | hu1
    · have hc : min (max 1 l) u = u := by
        rw [max_eq_left (le_trans hl ht)]; exact min_eq_right hu1
      rw [hc, max_eq_right hu1]
      refine le_trans ?_ (le_max_right _ _)
      nlinarith
    · have hc : min (max 1 l) u = 1 := by
        rw [max_eq_left (le_trans hl ht)]; exact min_eq_left hu1
      rw [hc, max_self]
      refine le_trans ?_ (le_max_right _ _)
      nlinarith
  · -- convex after `1`: below the chord from `a = max(1, l)` to `u`
    set a := max 1 l with ha
    have ha1 : 1 ≤ a := le_max_left _ _
    have hat : a ≤ t := max_le ht hl
    have hc : min a u = a := min_eq_left (le_trans hat hu)
    have hu1 : 1 ≤ u := le_trans ht hu
    rw [hc, max_eq_left ht, max_eq_left hu1, max_eq_left ha1]
    have ha0 : 0 < a := by linarith
    have ht0 : 0 < t := by linarith
    have hu0 : 0 < u := by linarith
    -- `1/t ≤ 1/a + 1/u - t/(a u)`
    have hchord : 1 / t ≤ 1 / a + 1 / u - t / (a * u) := by
      have hnum : 0 ≤ (t - a) * (u - t) := mul_nonneg (by linarith) (by linarith)
      have heq : 1 / a + 1 / u - t / (a * u) - 1 / t = (t - a) * (u - t) / (a * u * t) := by
        field_simp; ring
      have := div_nonneg hnum (by positivity : (0 : ℝ) ≤ a * u * t)
      linarith
    -- the chord is linear in `t`: at most its larger end
    have hau : 1 / a - t / (a * u) = (u - t) / (a * u) := by field_simp
    have hua : 1 / u - t / (a * u) = (a - t) / (a * u) := by field_simp
    rcases le_total 0 (-(1 / (a * u)) - m) with hs | hs
    · -- rising: at most `g(u)`
      refine le_trans ?_ (le_trans (le_max_right _ _) (le_max_left _ _))
      have : (u - t) * (-(1 / (a * u)) - m) ≥ 0 := mul_nonneg (by linarith) hs
      have h2 : (u - t) / (a * u) = (u - t) * (1 / (a * u)) := by ring
      nlinarith
    · -- falling: at most `g(a)`
      refine le_trans ?_ (le_max_right _ _)
      have : (t - a) * (-(1 / (a * u)) - m) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hs
      have h2 : (a - t) / (a * u) = (a - t) * (1 / (a * u)) := by ring
      nlinarith

/-- The real lower end: for `m ≤ 0`, `g` on `[l, u]` is at least the smaller of `g(l)` and
`2 √(-m)`. -/
private theorem aux_min_le {m l t : ℝ} (hm : m ≤ 0) (hl : l ≤ t) : -- --- CONCL ---
    min (1 / max l 1 - m * l) (2 * Real.sqrt (-m)) ≤ 1 / max t 1 - m * t := by -- --- PROOF ---
  rcases le_total t 1 with ht | ht
  · -- rising: `g(l)` is the least
    refine le_trans (min_le_left _ _) ?_
    rw [max_eq_right ht, max_eq_right (le_trans hl ht)]
    nlinarith
  · -- after `1`: `1/t + s² t - 2 s = (s t - 1)² / t`
    refine le_trans (min_le_right _ _) ?_
    rw [max_eq_left ht]
    set s := Real.sqrt (-m) with hs
    have hs2 : s * s = -m := Real.mul_self_sqrt (by linarith)
    have ht0 : 0 < t := by linarith
    have heq : 1 / t - m * t - 2 * s = (s * t - 1) ^ 2 / t := by
      field_simp; nlinarith
    have := div_nonneg (sq_nonneg (s * t - 1)) ht0.le
    linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem reciprocalRelaxation_encloses (p : ℕ) {w : 𝕋} (hw : 0 ≤ toReal w) : -- --- CONCL ---
    (reciprocalRelaxation p w).Encloses fun x => 1 / max x 1 := by -- --- PROOF ---
  -- the slope is negative: each quotient rounded up is positive
  have hslope : ∀ l u : 𝕋, toReal (step_reciprocalSlope l u) ≤ 0 := by
    intro l u
    unfold step_reciprocalSlope
    dsimp only
    have hl1 : 1 ≤ toReal (maximum l (one : 𝕋)) := by
      rw [toReal_maximum, toReal_one]; exact le_max_right _ _
    have hu1 : 1 ≤ toReal (maximum u (one : 𝕋)) := by
      rw [toReal_maximum, toReal_one]; exact le_max_right _ _
    have h1 := div_le_divUp one (maximum l one) (by linarith)
    have h2 := div_le_divUp one (maximum u one) (by linarith)
    rw [toReal_one] at h1 h2
    -- the product of two positive quotients, negated
    have h1' : 0 < 1 / toReal (maximum l (one : 𝕋)) := by positivity
    have h2' : 0 < 1 / toReal (maximum u (one : 𝕋)) := by positivity
    have h3 := mul_le_mulUp (divUp one (maximum l one)) (divUp one (maximum u one))
    rw [toReal_neg]
    nlinarith
  -- the band on every box, through `Relaxation.ofBand`
  have hW := Relaxation.ofBand_enclosesWhere (σ := fun x => 1 / max x 1) (P := fun _ _ => True)
    (s := step_reciprocalSlope) (lo := step_reciprocalLo p) (hi := step_reciprocalHi)
    (b := step_reciprocalMargin w) (fun {l u t} _ hl hu => ?_) (fun {l u} _ => ?_)
  · exact ⟨fun hl hu => hW.sound trivial hl hu⟩
  · set m := step_reciprocalSlope l u with hmdef
    have hm := hslope l u
    rw [← hmdef] at hm
    -- `1 / max(x, 1)` at a float, both ways
    have hup : ∀ x : 𝕋, 1 / max (toReal x) 1 - toReal m * toReal x
        ≤ toReal (subUp (divUp one (maximum x one)) (mulDown m x)) := by
      intro x
      have hx1 : 1 ≤ toReal (maximum x (one : 𝕋)) := by
        rw [toReal_maximum, toReal_one]; exact le_max_right _ _
      have h1 := div_le_divUp one (maximum x one) (by linarith)
      rw [toReal_one, toReal_maximum, toReal_one] at h1
      have h2 := sub_le_subUp (divUp one (maximum x one)) (mulDown m x)
      have h3 := mulDown_le_mul m x
      linarith
    -- the lower end, then the upper
    constructor
    · show toReal (step_reciprocalLo p l u) ≤ _
      unfold step_reciprocalLo
      rw [← hmdef]
      dsimp only
      rw [toReal_minimum]
      have hl1 : 1 ≤ toReal (maximum l (one : 𝕋)) := by
        rw [toReal_maximum, toReal_one]; exact le_max_right _ _
      have h1 := divDown_le_div one (maximum l one) (by linarith)
      rw [toReal_one, toReal_maximum, toReal_one] at h1
      have h2 := subDown_le_sub (divDown one (maximum l one)) (mulUp m l)
      have h3 := mul_le_mulUp m l
      -- `2 √(-m)` from below
      have h4 := sqrtDownCora_le p (neg m)
      rw [toReal_neg] at h4
      have h5 := addDown_le_add (sqrtDownCora p (neg m)) (sqrtDownCora p (neg m))
      have hmin := aux_min_le hm hl
      refine le_trans (min_le_min (by linarith) (by linarith)) hmin
    · -- the largest of the three values, each rounded up
      show _ ≤ toReal (step_reciprocalHi l u)
      unfold step_reciprocalHi
      rw [← hmdef]
      dsimp only
      rw [toReal_maximum, toReal_maximum]
      have hmax := aux_le_max hm hl hu
      have hL := hup l
      have hU := hup u
      have hC := hup (minimum (maximum one l) u)
      rw [toReal_minimum, toReal_maximum, toReal_one] at hC
      refine le_trans hmax (max_le_max (max_le_max hL hU) hC)
  · -- the margin: `1` and `|m| max(|l|, |u|)` are not negative
    unfold step_reciprocalMargin
    dsimp only
    set m := step_reciprocalSlope l u
    have hk : 0 ≤ toReal (maximum (absolute l) (absolute u)) := by
      rw [toReal_maximum, toReal_absolute]; exact le_trans (abs_nonneg _) (le_max_left _ _)
    have hm : 0 ≤ toReal (absolute m) := by rw [toReal_absolute]; exact abs_nonneg _
    have h1 := mul_le_mulUp (absolute m) (maximum (absolute l) (absolute u))
    have h2 := add_le_addUp one (mulUp (absolute m) (maximum (absolute l) (absolute u)))
    have h3 := mul_le_mulUp (addUp one (mulUp (absolute m) (maximum (absolute l) (absolute u)))) w
    rw [toReal_one] at h2
    have hpos : 0 ≤ toReal (addUp one
        (mulUp (absolute m) (maximum (absolute l) (absolute u)))) := by nlinarith
    nlinarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
