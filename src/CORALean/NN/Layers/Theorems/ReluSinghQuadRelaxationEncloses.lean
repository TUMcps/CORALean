module

public import CORALean.NN.Layers.Operations.ReluSinghQuadRelaxation
public import CORALean.NN.Layers.Theorems.ReluRelaxationEncloses
public import CORALean.NN.Layers.Theorems.Basic
public import CORALean.NN.Layers.Definitions.Relu

@[expose] public section

/-!
# The quadratic ReLU fit encloses ReLU

On a piece `[x₀, x₁]` the quadratic `q(t) = (a t + β) t + c` with `a > 0` lies below the larger end
value (it lies below its chord, `q - chord = a (t - x₀)(t - x₁)`) and above `c - β²/(4a)`, which is
`a (t + β/(2a))²` below it; where the vertex `-β/(2a)` is certified outside the piece, `q` is
monotone on it and above the nearer end. So `p - relu` lies in the band on both pieces, and moving
`c` by the middle leaves an error of at most the larger distance plus the rounding of `c - m`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* `reluSinghQuadRelaxation` encloses ReLU on every box
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A float product from below, at any signs: below both `v x` for `v` the ends of a range. -/
private theorem aux_mul_range_down {vd vu x : 𝕋} {v : ℝ} (hd : toReal vd ≤ v)
    (hu : v ≤ toReal vu) : -- --- CONCL ---
    toReal (minimum (mulDown vd x) (mulDown vu x)) ≤ v * toReal x := by -- --- PROOF ---
  rw [toReal_minimum]
  rcases le_total 0 (toReal x) with hx | hx
  · exact le_trans (min_le_left _ _)
      (le_trans (mulDown_le_mul vd x) (mul_le_mul_of_nonneg_right hd hx))
  · exact le_trans (min_le_right _ _)
      (le_trans (mulDown_le_mul vu x) (mul_le_mul_of_nonpos_right hu hx))

/-- And from above. -/
private theorem aux_mul_range_up {vd vu x : 𝕋} {v : ℝ} (hd : toReal vd ≤ v)
    (hu : v ≤ toReal vu) : -- --- CONCL ---
    v * toReal x ≤ toReal (maximum (mulUp vd x) (mulUp vu x)) := by -- --- PROOF ---
  rw [toReal_maximum]
  rcases le_total 0 (toReal x) with hx | hx
  · exact le_trans (mul_le_mul_of_nonneg_right hu hx)
      (le_trans (mul_le_mulUp vu x) (le_max_right _ _))
  · exact le_trans (mul_le_mul_of_nonpos_right hd hx)
      (le_trans (mul_le_mulUp vd x) (le_max_left _ _))

/-- Horner's `(a x + β) x + c` between `step_quadDown` and `step_quadUp`, for `β ∈ [bd, bu]`. -/
private theorem aux_quad_bounds {a bd bu c x : 𝕋} {β : ℝ} (h₁ : toReal bd ≤ β)
    (h₂ : β ≤ toReal bu) : -- --- CONCL ---
    toReal (step_quadDown a bd bu c x) ≤ (toReal a * toReal x + β) * toReal x + toReal c ∧
      (toReal a * toReal x + β) * toReal x + toReal c ≤
        toReal (step_quadUp a bd bu c x) := by -- --- PROOF ---
  have hd : toReal (addDown (mulDown a x) bd) ≤ toReal a * toReal x + β := by
    have := addDown_le_add (mulDown a x) bd; have := mulDown_le_mul a x; linarith
  have hu : toReal a * toReal x + β ≤ toReal (addUp (mulUp a x) bu) := by
    have := add_le_addUp (mulUp a x) bu; have := mul_le_mulUp a x; linarith
  have e₁ := aux_mul_range_down (x := x) hd hu
  have e₂ := aux_mul_range_up (x := x) hd hu
  constructor
  · unfold step_quadDown
    have := addDown_le_add (minimum (mulDown (addDown (mulDown a x) bd) x)
      (mulDown (addUp (mulUp a x) bu) x)) c
    linarith
  · unfold step_quadUp
    have := add_le_addUp (maximum (mulUp (addDown (mulDown a x) bd) x)
      (mulUp (addUp (mulUp a x) bu) x)) c
    linarith

/-- The vertex value from below lies below the quadratic everywhere, for `a > 0`. -/
private theorem aux_vertex_le {a bd bu c : 𝕋} {β : ℝ} (ha : 0 < toReal a) (h₁ : toReal bd ≤ β)
    (h₂ : β ≤ toReal bu) (t : ℝ) : -- --- CONCL ---
    toReal (step_quadVertexDown a bd bu c) ≤
      (toReal a * t + β) * t + toReal c := by -- --- PROOF ---
  have hsq : β * β ≤ toReal (maximum (mulUp bd bd) (mulUp bu bu)) := by
    rw [toReal_maximum]
    rcases le_total 0 β with hb | hb
    · exact le_trans (by nlinarith) (le_trans (mul_le_mulUp bu bu) (le_max_right _ _))
    · exact le_trans (by nlinarith) (le_trans (mul_le_mulUp bd bd) (le_max_left _ _))
  have hdiv := div_le_divUp (maximum (mulUp bd bd) (mulUp bu bu)) a ha
  have hq : (β * β) / toReal a ≤ toReal (maximum (mulUp bd bd) (mulUp bu bu)) / toReal a :=
    div_le_div_of_nonneg_right hsq ha.le
  -- a (t + β/(2a))² ≥ 0 is the quadratic minus the vertex value
  have hv : toReal c - (β * β) / toReal a / 4 ≤ (toReal a * t + β) * t + toReal c := by
    have h0 : 0 ≤ (2 * toReal a * t + β) ^ 2 / (4 * toReal a) := by positivity
    have : (2 * toReal a * t + β) ^ 2 / (4 * toReal a) =
        (toReal a * t + β) * t + β * β / toReal a / 4 := by field_simp; ring
    linarith
  unfold step_quadVertexDown
  have := addDown_le_add c (neg (half (half (divUp (maximum (mulUp bd bd) (mulUp bu bu)) a))))
  simp only [subDown, toReal_neg, toReal_half] at this ⊢
  linarith

/-- The least end or vertex value of `step_quadRange` lies below the quadratic on its piece. -/
private theorem aux_range_lo {a bd bu c x₀ x₁ : 𝕋} {β t : ℝ} (ha : 0 < toReal a)
    (h₁ : toReal bd ≤ β) (h₂ : β ≤ toReal bu) (ht₀ : toReal x₀ ≤ t)
    (ht₁ : t ≤ toReal x₁) : -- --- CONCL ---
    toReal (step_quadRange a bd bu c x₀ x₁).1 ≤
      (toReal a * t + β) * t + toReal c := by -- --- PROOF ---
  set q := fun s : ℝ => (toReal a * s + β) * s + toReal c with hq
  have e₀ := (aux_quad_bounds (a := a) (c := c) (x := x₀) h₁ h₂).1
  have e₁ := (aux_quad_bounds (a := a) (c := c) (x := x₁) h₁ h₂).1
  have hlo : toReal (minimum (step_quadDown a bd bu c x₀) (step_quadDown a bd bu c x₁)) ≤
      min (q (toReal x₀)) (q (toReal x₁)) := by
    rw [toReal_minimum]; exact min_le_min e₀ e₁
  unfold step_quadRange
  split
  · rw [toReal_minimum]
    exact le_trans (min_le_right _ _) (aux_vertex_le ha h₁ h₂ t)
  · -- the vertex certified below `x₀` or above `x₁`: `q` is monotone on the piece
    rename_i hin
    have hin' : ltStrict (half (divUp (neg bd) a)) x₀ = true ∨
        ltStrict x₁ (half (divDown (neg bu) a)) = true := by
      unfold step_quadVertexIn at hin
      cases h1 : ltStrict (half (divUp (neg bd) a)) x₀ <;>
        cases h2 : ltStrict x₁ (half (divDown (neg bu) a)) <;> simp_all
    refine le_trans hlo ?_
    rcases hin' with h | h
    · have hr := toReal_lt_of_ltStrict h
      have hdu := div_le_divUp (neg bd) a ha
      rw [toReal_half] at hr
      rw [toReal_neg] at hdu
      have hv : -β / toReal a ≤ -toReal bd / toReal a :=
        div_le_div_of_nonneg_right (by linarith) ha.le
      -- `x₀` above the vertex: `2 a x₀ + β > 0`
      have hpos : 0 < 2 * toReal a * toReal x₀ + β := by
        have : -β / toReal a < 2 * toReal x₀ := by linarith
        rw [div_lt_iff₀ ha] at this; linarith
      have : q (toReal x₀) ≤ q t := by
        simp only [hq]; nlinarith [mul_nonneg (sub_nonneg.2 ht₀) ha.le]
      exact le_trans (min_le_left _ _) this
    · have hr := toReal_lt_of_ltStrict h
      have hdd := divDown_le_div (neg bu) a ha
      rw [toReal_half] at hr
      rw [toReal_neg] at hdd
      have hv : -toReal bu / toReal a ≤ -β / toReal a :=
        div_le_div_of_nonneg_right (by linarith) ha.le
      have hneg : 2 * toReal a * toReal x₁ + β < 0 := by
        have : 2 * toReal x₁ < -β / toReal a := by linarith
        rw [lt_div_iff₀ ha] at this; linarith
      have : q (toReal x₁) ≤ q t := by
        simp only [hq]; nlinarith [mul_nonneg (sub_nonneg.2 ht₁) ha.le]
      exact le_trans (min_le_right _ _) this

/-- The largest end value lies above the quadratic on its piece: it lies below its chord. -/
private theorem aux_range_hi {a bd bu c x₀ x₁ : 𝕋} {β t : ℝ} (ha : 0 ≤ toReal a)
    (h₁ : toReal bd ≤ β) (h₂ : β ≤ toReal bu) (ht₀ : toReal x₀ ≤ t)
    (ht₁ : t ≤ toReal x₁) : -- --- CONCL ---
    (toReal a * t + β) * t + toReal c ≤
      toReal (step_quadRange a bd bu c x₀ x₁).2 := by -- --- PROOF ---
  have e₀ := (aux_quad_bounds (a := a) (c := c) (x := x₀) h₁ h₂).2
  have e₁ := (aux_quad_bounds (a := a) (c := c) (x := x₁) h₁ h₂).2
  unfold step_quadRange
  simp only [toReal_maximum]
  set M := max (toReal (step_quadUp a bd bu c x₀)) (toReal (step_quadUp a bd bu c x₁))
  have hM₀ : (toReal a * toReal x₀ + β) * toReal x₀ + toReal c ≤ M := le_trans e₀ (le_max_left _ _)
  have hM₁ : (toReal a * toReal x₁ + β) * toReal x₁ + toReal c ≤ M := le_trans e₁ (le_max_right _ _)
  -- (x₁ - x₀) q(t) = (x₁ - t) q(x₀) + (t - x₀) q(x₁) - a (t - x₀)(x₁ - t)(x₁ - x₀)
  rcases eq_or_lt_of_le (le_trans ht₀ ht₁) with he | hlt
  · have : t = toReal x₀ := le_antisymm (he ▸ ht₁) ht₀
    rw [this]; exact hM₀
  · have hw : 0 < toReal x₁ - toReal x₀ := by linarith
    have key : (toReal x₁ - toReal x₀) * ((toReal a * t + β) * t + toReal c) ≤
        (toReal x₁ - toReal x₀) * M := by
      have hc : 0 ≤ toReal a * (t - toReal x₀) * (toReal x₁ - t) * (toReal x₁ - toReal x₀) := by
        have := mul_nonneg (sub_nonneg.2 ht₀) (sub_nonneg.2 ht₁)
        positivity
      nlinarith [mul_le_mul_of_nonneg_left hM₀ (sub_nonneg.2 ht₁),
        mul_le_mul_of_nonneg_left hM₁ (sub_nonneg.2 ht₀)]
    exact le_of_mul_le_mul_left key hw

/-- `p - relu` in the band on the box, for the parabola's case. -/
private theorem aux_band {l u : 𝕋} {t : ℝ} (ha : 0 < toReal (step_reluQuadCoeffs l u).1)
    (hl : toReal l ≤ t) (hu : t ≤ toReal u) : -- --- CONCL ---
    toReal (step_reluQuadBand l u).1 ≤
        (toReal (step_reluQuadCoeffs l u).1 * t + toReal (step_reluQuadCoeffs l u).2.1) * t +
          toReal (step_reluQuadCoeffs l u).2.2 - Real.relu t ∧
      (toReal (step_reluQuadCoeffs l u).1 * t + toReal (step_reluQuadCoeffs l u).2.1) * t +
          toReal (step_reluQuadCoeffs l u).2.2 - Real.relu t ≤
            toReal (step_reluQuadBand l u).2 := by -- --- PROOF ---
  set a := (step_reluQuadCoeffs l u).1
  set b := (step_reluQuadCoeffs l u).2.1
  set c := (step_reluQuadCoeffs l u).2.2
  unfold step_reluQuadBand
  simp only [toReal_minimum, toReal_maximum]
  rcases le_total t 0 with h0 | h0
  · -- on `[l, 0]` ReLU is zero
    have hr : Real.relu t = 0 := max_eq_right h0
    have ht₁ : t ≤ toReal (zero : 𝕋) := by rw [toReal_zero]; exact h0
    have lo := aux_range_lo (bd := b) (bu := b) (β := toReal b) (c := c) ha le_rfl le_rfl hl ht₁
    have hi := aux_range_hi (bd := b) (bu := b) (β := toReal b) (c := c) ha.le le_rfl le_rfl hl ht₁
    rw [hr, sub_zero]
    exact ⟨le_trans (min_le_left _ _) lo, le_trans hi (le_max_left _ _)⟩
  · -- on `[0, u]` it is `t`, and `b - 1` lies between its two roundings
    have hr : Real.relu t = t := max_eq_left h0
    have ht₀ : toReal (zero : 𝕋) ≤ t := by rw [toReal_zero]; exact h0
    have hbd : toReal (subDown b one) ≤ toReal b - 1 := by
      have := addDown_le_add b (neg one); simp only [subDown, toReal_neg, toReal_one] at *
      linarith
    have hbu : toReal b - 1 ≤ toReal (subUp b one) := by
      have := add_le_addUp b (neg one); simp only [subUp, toReal_neg, toReal_one] at *
      linarith
    have lo := aux_range_lo (c := c) ha hbd hbu ht₀ hu
    have hi := aux_range_hi (c := c) ha.le hbd hbu ht₀ hu
    rw [hr]
    constructor
    · exact le_trans (min_le_right _ _) (by linarith)
    · exact le_trans (by linarith) (le_max_right _ _)


-- =======================================  MAIN THEOREM  ======================================= --

theorem reluSinghQuadRelaxation_encloses : -- --- CONCL ---
    (reluSinghQuadRelaxation (𝕋 := 𝕋)).Encloses Real.relu := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  -- what each case of the box certifies
  have h₀ : step_reluQuadCase l u = 0 → t ≤ 0 := fun h => by
    unfold step_reluQuadCase at h
    by_cases hu0 : le u zero = true
    · exact le_trans hu (toReal_zero (𝕋 := 𝕋) ▸ toReal_le_of_le hu0)
    · by_cases hl0 : le zero l = true
      · simp [hu0, hl0] at h
      · simp [hu0, hl0] at h; split_ifs at h
  -- case 1 certifies `0 ≤ l`, case 2 a positive `a`
  have h₁ : step_reluQuadCase l u = 1 → 0 ≤ t := fun h => by
    unfold step_reluQuadCase at h
    by_cases hu0 : le u zero = true
    · simp [hu0] at h
    by_cases hl0 : le zero l = true
    · exact le_trans (toReal_zero (𝕋 := 𝕋) ▸ toReal_le_of_le hl0) hl
    · simp [hu0, hl0] at h; split_ifs at h <;> omega
  have h₂ : step_reluQuadCase l u = 2 → 0 < toReal (step_reluQuadCoeffs l u).1 := fun h => by
    unfold step_reluQuadCase at h
    by_cases hu0 : le u zero = true
    · simp [hu0] at h
    by_cases hl0 : le zero l = true
    · simp [hu0, hl0] at h
    by_cases ha0 : ltStrict zero (step_reluQuadCoeffs l u).1 = true
    · have := toReal_lt_of_ltStrict ha0; rwa [toReal_zero] at this
    · simp [hu0, hl0, ha0] at h
  simp only [reluSinghQuadRelaxation]
  match hk : step_reluQuadCase l u with
  | 0 =>
    -- ReLU is zero on the box
    simp [Real.evalPoly, Fin.sum_univ_three, toReal_zero, Real.relu,
      max_eq_right (h₀ hk)]
  | 1 =>
    -- ReLU is the identity on the box
    simp [Real.evalPoly, Fin.sum_univ_three, toReal_zero, toReal_one,
      Real.relu, max_eq_left (h₁ hk)]
  | 2 =>
    -- the parabola: the band, moved by its middle
    have ha := h₂ hk
    obtain ⟨hlo, hhi⟩ := aux_band ha hl hu
    set a := (step_reluQuadCoeffs l u).1
    set b := (step_reluQuadCoeffs l u).2.1
    set c := (step_reluQuadCoeffs l u).2.2
    set m := step_reluQuadMid l u
    set lo := (step_reluQuadBand l u).1
    set hi := (step_reluQuadBand l u).2
    -- the roundings of `c - m`, of the distances to the ends and of the gap
    have hc₁ := addDown_le_add c (neg m)
    have hc₂ := add_le_addUp c (neg m)
    have hg := add_le_addUp (subUp c m) (neg (subDown c m))
    have hD₁ := add_le_addUp hi (neg m)
    have hD₂ := add_le_addUp m (neg lo)
    simp only [subDown, subUp, toReal_neg] at hc₁ hc₂ hg hD₁ hD₂
    have hpoly : Real.evalPoly (fun k => toReal (![subDown c m, b, a] k)) t =
        toReal (subDown c m) + toReal b * t + toReal a * t ^ 2 := by
      simp [Real.evalPoly, Fin.sum_univ_three]
    simp only [hpoly]
    -- the error is the larger distance plus the gap
    have hD : toReal (subUp hi m) ≤ toReal (maximum (subUp hi m) (subUp m lo)) ∧
        toReal (subUp m lo) ≤ toReal (maximum (subUp hi m) (subUp m lo)) := by
      rw [toReal_maximum]; exact ⟨le_max_left _ _, le_max_right _ _⟩
    simp only [subUp] at hD
    have hb : |Real.relu t - (toReal (subDown c m) + toReal b * t + toReal a * t ^ 2)| ≤
        toReal (maximum (subUp hi m) (subUp m lo)) + toReal (subUp (subUp c m) (subDown c m)) := by
      have e : (toReal a * t + toReal b) * t = toReal b * t + toReal a * t ^ 2 := by ring
      rw [e] at hlo hhi
      simp only [subUp, subDown]
      rw [abs_le]; constructor <;> linarith
    -- a certified zero gap is left out
    split_ifs with hz
    · have : toReal (subUp (subUp c m) (subDown c m)) ≤ 0 := by
        have := toReal_le_of_le hz; rwa [toReal_zero] at this
      linarith
    · exact le_trans hb (add_le_addUp _ _)
  | k + 3 =>
    -- the fallback line
    simpa [PolyRelaxation.padTo, Relaxation.toPoly] using
      (PolyRelaxation.padTo_encloses (M := 2) (by norm_num)
        (Relaxation.toPoly_encloses (reluRelaxation_encloses (𝕋 := 𝕋) reluSlope))).sound hl hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
