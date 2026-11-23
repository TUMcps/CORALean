module

public import CORALean.NN.Layers.Operations.InverseRelaxation
public import CORALean.NN.Layers.Theorems.OfBandEnclosesWhere
public import CORALean.Global.Float.SqrtDownCoraLe

@[expose] public section

/-!
# The chord relaxation of the inverse is sound

On a box `[l, u]` with `0 < l`, `1/x` is below its chord, `(x - l)(u - x) ≥ 0`, so
`g(x) = 1/x - m x` is at most a linear function of `x` that agrees with `g` at both ends: at most
the larger of `g(l)` and `g(u)`. The stored slope `m` is not positive, and below, `g` is at least
`2 √(-m)` by `1/x + s² x - 2 s = (s x - 1)² / x` at `s = √(-m)`. The margin is not negative, so
`Relaxation.ofBand_enclosesWhere` concludes on every box with `0 < l`.

## Inputs
* `p` – the square root's Newton steps
* `w` – the margin's factor

## Hypotheses
* `hw` – the factor is not negative

## Conclusion
* the relaxation is sound for `x ↦ 1 / x` on every box above zero
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

/-- The real upper end: on `[l, u]` with `0 < l`, `1/t - m t` is at most its larger end. -/
private theorem aux_le_max {m l u t : ℝ} (hl0 : 0 < l) (hl : l ≤ t) (hu : t ≤ u) : -- --- CONCL ---
    1 / t - m * t ≤ max (1 / l - m * l) (1 / u - m * u) := by -- --- PROOF ---
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := by linarith
  -- `1/t ≤ 1/l + 1/u - t/(l u)`
  have hchord : 1 / t ≤ 1 / l + 1 / u - t / (l * u) := by
    have hnum : 0 ≤ (t - l) * (u - t) := mul_nonneg (by linarith) (by linarith)
    have heq : 1 / l + 1 / u - t / (l * u) - 1 / t = (t - l) * (u - t) / (l * u * t) := by
      field_simp; ring
    have := div_nonneg hnum (by positivity : (0 : ℝ) ≤ l * u * t)
    linarith
  -- the chord less `m t` is linear in `t`: at most its larger end
  have hlu : 1 / l - t / (l * u) = (u - t) / (l * u) := by field_simp
  have hul : 1 / u - t / (l * u) = (l - t) / (l * u) := by field_simp
  rcases le_total 0 (-(1 / (l * u)) - m) with hs | hs
  · -- rising: at most `g(u)`
    refine le_trans ?_ (le_max_right _ _)
    have : (u - t) * (-(1 / (l * u)) - m) ≥ 0 := mul_nonneg (by linarith) hs
    have h2 : (u - t) / (l * u) = (u - t) * (1 / (l * u)) := by ring
    nlinarith
  · -- falling: at most `g(l)`
    refine le_trans ?_ (le_max_left _ _)
    have : (t - l) * (-(1 / (l * u)) - m) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hs
    have h2 : (l - t) / (l * u) = (l - t) * (1 / (l * u)) := by ring
    nlinarith

/-- The real lower end: for `m ≤ 0` and `t > 0`, `1/t - m t` is at least `2 √(-m)`. -/
private theorem aux_min_le {m t : ℝ} (hm : m ≤ 0) (ht0 : 0 < t) : -- --- CONCL ---
    2 * Real.sqrt (-m) ≤ 1 / t - m * t := by -- --- PROOF ---
  set s := Real.sqrt (-m) with hs
  have hs2 : s * s = -m := Real.mul_self_sqrt (by linarith)
  -- `1/t + s² t - 2 s = (s t - 1)² / t`
  have heq : 1 / t - m * t - 2 * s = (s * t - 1) ^ 2 / t := by
    field_simp; nlinarith
  have := div_nonneg (sq_nonneg (s * t - 1)) ht0.le
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem inverseRelaxation_encloses (p : ℕ) {w : 𝕋} (hw : 0 ≤ toReal w) : -- --- CONCL ---
    (inverseRelaxation p w).EnclosesWhere (fun x => 1 / x) fun l _ =>
      0 < toReal l := by -- --- PROOF ---
  -- above zero both quotients rounded up are positive, so the slope is not positive
  have hslope : ∀ l u : 𝕋, 0 < toReal l → toReal l ≤ toReal u →
      toReal (step_inverseSlope l u) ≤ 0 := by
    intro l u hl hlu
    unfold step_inverseSlope
    have h1 := div_le_divUp one l hl
    have h2 := div_le_divUp one u (by linarith)
    rw [toReal_one] at h1 h2
    have h1' : 0 < 1 / toReal l := by positivity
    have h2' : 0 < 1 / toReal u := one_div_pos.mpr (by linarith)
    have h3 := mul_le_mulUp (divUp one l) (divUp one u)
    rw [toReal_neg]
    nlinarith
  refine Relaxation.ofBand_enclosesWhere (fun {l u t} hP hl hu => ?_) (fun {l u} hP => ?_)
  · have hl0 : 0 < toReal l := hP
    have ht0 : 0 < t := by linarith
    set m := step_inverseSlope l u with hmdef
    have hm := hslope l u hl0 (le_trans hl hu)
    rw [← hmdef] at hm
    -- `1 / x` at a float above zero, from above
    have hup : ∀ x : 𝕋, 0 < toReal x → 1 / toReal x - toReal m * toReal x
        ≤ toReal (subUp (divUp one x) (mulDown m x)) := by
      intro x hx
      have h1 := div_le_divUp one x hx
      rw [toReal_one] at h1
      have h2 := sub_le_subUp (divUp one x) (mulDown m x)
      have h3 := mulDown_le_mul m x
      linarith
    constructor
    · -- `2 √(-m)` from below
      show toReal (step_inverseLo p l u) ≤ _
      unfold step_inverseLo
      rw [← hmdef]
      dsimp only
      have h4 := sqrtDownCora_le p (neg m)
      rw [toReal_neg] at h4
      have h5 := addDown_le_add (sqrtDownCora p (neg m)) (sqrtDownCora p (neg m))
      have hmin := aux_min_le hm ht0
      linarith
    · -- the larger of the two ends, each rounded up
      show _ ≤ toReal (step_inverseHi l u)
      unfold step_inverseHi
      rw [← hmdef]
      dsimp only
      rw [toReal_maximum]
      exact le_trans (aux_le_max hl0 hl hu)
        (max_le_max (hup l hl0) (hup u (by linarith)))
  · -- the margin: `1 / l` rounded up is positive
    have hl0 : 0 < toReal l := hP
    unfold step_inverseMargin
    have h1 := div_le_divUp one l hl0
    rw [toReal_one] at h1
    have h1' : 0 < 1 / toReal l := by positivity
    have h3 := mul_le_mulUp (divUp one l) w
    nlinarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
