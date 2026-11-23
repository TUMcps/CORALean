module

public import CORALean.NN.Layers.Operations.TrigRelaxation
public import CORALean.NN.Layers.Theorems.OfBandEnclosesWhere
public import CORALean.Global.TaylorRemainder
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# The relaxation of sine and cosine is sound

Write `f(x) = sin(x + δ)`, `δ = 0` for `sin` and `π / 2` for `cos`. The tangent at `c` is off by
at most `(x - c)² / 2` (Taylor, `|f''| ≤ 1`), and the roundings of `f(c)`, `f'(c)` and the offset
are charged to the error. On the box, a maximum of `f` inside `[l, u]` is a peak `π/2 - δ + 2π k`.
The test finds an integer between the quotients whenever a peak lies in the box: the quotients
are bounds of `(l - a) / 2π` and `(u - a) / 2π`, from a bracket of `π`. So where it finds none,
`f` is at most its larger end value; the same holds for the minima. The band then encloses `f`,
and so does the relaxation, whichever line it takes.

## Inputs
* `cosine` – `cos`, else `sin`
* `n` – the halvings of `sin` and `cos`
* `w` – the margin's factor
* `w₁` – the box's margin factor
* `w₄` – the half width's widening

## Hypotheses
* `hw` – `w` is not negative
* `hw₁` – `w₁` is not negative
* `hw₄` – `w₄` is not negative

## Conclusion
* the relaxation is sound for `cos` (`cosine`) or `sin`
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic _root_.Real

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The tangent of `sin(x + δ)` at `c` is off by at most `(x - c)² / 2`. -/
private theorem aux_taylor (δ c x : ℝ) : -- --- CONCL ---
    |sin (x + δ) - (sin (c + δ) + cos (c + δ) * (x - c))| ≤ (x - c) ^ 2 / 2 := by -- --- PROOF ---
  have hd1 : deriv (fun y => sin (y + δ)) = fun y => cos (y + δ) := by
    funext y
    exact ((hasDerivAt_sin _).comp y ((hasDerivAt_id y).add_const δ)).deriv.trans (by simp)
  have hd2 : deriv (fun y => cos (y + δ)) = fun y => -sin (y + δ) := by
    funext y
    exact ((hasDerivAt_cos _).comp y ((hasDerivAt_id y).add_const δ)).deriv.trans (by simp)
  have h := taylor_remainder_abs_le (g := fun y => sin (y + δ)) (N := 1) (c := c) (x := x)
    (D := 1) (fun ξ _ => (contDiff_sin.comp (contDiff_id.add contDiff_const)).contDiffAt)
    (fun ξ _ => by
      rw [iteratedDeriv_succ, iteratedDeriv_one, hd1, hd2, abs_neg]; exact abs_sin_le_one _)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDeriv_zero, iteratedDeriv_one,
    hd1] at h
  norm_num at h
  exact h

/-- Without a peak `π/2 - δ + 2π k` in `[l, u]`, `sin(t + δ)` there is at most its larger end. -/
private theorem aux_no_peak {δ l u t : ℝ}
    (h : ∀ k : ℤ, ¬ (l ≤ π / 2 - δ + 2 * π * k ∧ π / 2 - δ + 2 * π * k ≤ u)) (hl : l ≤ t)
    (hu : t ≤ u) : -- --- CONCL ---
    sin (t + δ) ≤ max (sin (l + δ)) (sin (u + δ)) := by -- --- PROOF ---
  by_contra H
  push Not at H
  -- the largest value over the box, at a point strictly inside it
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (le_trans hl hu))
    (Continuous.continuousOn (f := fun y => sin (y + δ)) (by fun_prop))
  have hxt : sin (t + δ) ≤ sin (x + δ) := hmax ⟨hl, hu⟩
  have hgl : sin (l + δ) < sin (x + δ) := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) H) hxt
  have hgu : sin (u + δ) < sin (x + δ) := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) H) hxt
  have hxl : l < x := lt_of_le_of_ne hx.1 (by rintro rfl; exact lt_irrefl _ hgl)
  have hxu : x < u := lt_of_le_of_ne hx.2 (by rintro rfl; exact lt_irrefl _ hgu)
  -- there the derivative vanishes, so the value is `±1`
  have hloc : IsLocalMax (fun y => sin (y + δ)) x := hmax.isLocalMax (Icc_mem_nhds hxl hxu)
  have hd : HasDerivAt (fun y => sin (y + δ)) (cos (x + δ)) x := by
    simpa using ((hasDerivAt_id x).add_const δ).sin
  have hc : cos (x + δ) = 0 := hloc.hasDerivAt_eq_zero hd
  have hpm : (sin (x + δ) - 1) * (sin (x + δ) + 1) = 0 := by
    nlinarith [sin_sq_add_cos_sq (x + δ)]
  rcases mul_eq_zero.mp hpm with h1 | h1
  · -- `1`: a peak
    have h2 : cos (x + δ - π / 2) = 1 := by rw [cos_sub_pi_div_two]; linarith
    obtain ⟨k, hk⟩ := (cos_eq_one_iff _).mp h2
    exact h k ⟨by linarith, by linarith⟩
  · -- `-1`: no more than the end
    linarith [neg_one_le_sin (l + δ)]

/-- Without a trough `-π/2 - δ + 2π k` in `[l, u]`, `sin(t + δ)` is at least its smaller end. -/
private theorem aux_no_trough {δ l u t : ℝ}
    (h : ∀ k : ℤ, ¬ (l ≤ -(π / 2) - δ + 2 * π * k ∧ -(π / 2) - δ + 2 * π * k ≤ u))
    (hl : l ≤ t) (hu : t ≤ u) : -- --- CONCL ---
    min (sin (l + δ)) (sin (u + δ)) ≤ sin (t + δ) := by -- --- PROOF ---
  have hneg : ∀ y, sin (y + (δ + π)) = -sin (y + δ) := fun y => by
    rw [← add_assoc, sin_add_pi]
  have := aux_no_peak (δ := δ + π) (fun k hk => h k ⟨by linarith [hk.1], by linarith [hk.2]⟩) hl hu
  rw [hneg, hneg, hneg] at this
  rcases le_total (sin (l + δ)) (sin (u + δ)) with h' | h'
  · rw [min_eq_left h']; rw [max_eq_left (neg_le_neg h')] at this; linarith
  · rw [min_eq_right h']; rw [max_eq_right (neg_le_neg h')] at this; linarith

omit [ToRat 𝕋] in
/-- `half^[k] one` is `2⁻ᵏ`. -/
private theorem aux_half_pow (k : ℕ) :
    toReal (half^[k] (one : 𝕋)) = (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => simp [toReal_one]
  | succ k ih => rw [Function.iterate_succ_apply', toReal_half, ih, pow_succ]; ring

omit [ToRat 𝕋] in
/-- The bits' sum, either way. -/
private theorem aux_bits (L : List ℕ) : -- --- CONCL ---
    toReal (L.foldr (fun k s => addDown (half^[k] (one : 𝕋)) s) zero)
        ≤ (L.map fun k => (1 / 2 : ℝ) ^ k).sum ∧
      (L.map fun k => (1 / 2 : ℝ) ^ k).sum
        ≤ toReal (L.foldr (fun k s => addUp (half^[k] (one : 𝕋)) s) zero) := by -- --- PROOF ---
  induction L with
  | nil => simp [toReal_zero]
  | cons k L ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    have h1 := addDown_le_add (half^[k] (one : 𝕋))
      (L.foldr (fun k s => addDown (half^[k] (one : 𝕋)) s) zero)
    have h2 := add_le_addUp (half^[k] (one : 𝕋))
      (L.foldr (fun k s => addUp (half^[k] (one : 𝕋)) s) zero)
    rw [aux_half_pow] at h1 h2
    exact ⟨by linarith [ih.1], by linarith [ih.2]⟩

omit [ToRat 𝕋] in
/-- The bracket of `π`. -/
private theorem aux_pi : -- --- CONCL ---
    toReal (step_trigPiDown (𝕋 := 𝕋)) ≤ π ∧ π ≤ toReal (step_trigPiUp
      (𝕋 := 𝕋)) := by -- --- PROOF ---
  have hs : (step_trigPiBits.map fun k => (1 / 2 : ℝ) ^ k).sum = 884279719003555 / 2 ^ 49 := by
    simp only [step_trigPiBits, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    norm_num
  -- the sums either way, against Mathlib's twenty digits of `π`
  obtain ⟨hd, hu⟩ := aux_bits (𝕋 := 𝕋) step_trigPiBits
  rw [hs] at hd hu
  have hlo := pi_gt_d20
  have hhi := pi_lt_d20
  constructor
  · unfold step_trigPiDown
    dsimp only
    refine le_trans (addDown_le_add _ _) ?_
    norm_num at hlo
    linarith
  · -- above: the doubled sum and `3 · 2⁻⁵⁴`
    unfold step_trigPiUp
    dsimp only
    refine le_trans ?_ (add_le_addUp _ _)
    have h1 := add_le_addUp (step_trigPiBits.foldr (fun k s => addUp (half^[k] (one : 𝕋)) s) zero)
      (step_trigPiBits.foldr (fun k s => addUp (half^[k] (one : 𝕋)) s) zero)
    set e := addUp (half^[53] (one : 𝕋)) (half^[54] (one : 𝕋)) with he
    have h2 : (3 : ℝ) / 2 ^ 54 ≤ toReal e := by
      have h3 := add_le_addUp (half^[53] (one : 𝕋)) (half^[54] (one : 𝕋))
      rw [aux_half_pow, aux_half_pow, ← he] at h3
      linarith
    norm_num at hhi
    linarith

/-- The shift `δ` with `f(x) = sin(x + δ)`. -/
private noncomputable def aux_shift (cosine : Bool) : ℝ := if cosine then π / 2 else 0

/-- `cos` and `sin` as `sin(x + δ)`. -/
private theorem aux_f (cosine : Bool) (x : ℝ) :
    (if cosine then cos x else sin x) = sin (x + aux_shift cosine) := by
  cases cosine <;> simp [aux_shift, sin_add_pi_div_two]

omit [ToRat 𝕋] in
/-- The peaks' bracket holds the real peak `π/2 - δ` (`π` more for the troughs). -/
private theorem aux_peak (cosine bottom : Bool) : -- --- CONCL ---
    toReal (step_trigPeak (𝕋 := 𝕋) cosine bottom).1
        ≤ π / 2 - aux_shift cosine + (if bottom then π else 0) ∧
      π / 2 - aux_shift cosine + (if bottom then π else 0)
        ≤ toReal (step_trigPeak (𝕋 := 𝕋) cosine bottom).2 := by -- --- PROOF ---
  obtain ⟨hpL, hpU⟩ := aux_pi (𝕋 := 𝕋)
  unfold step_trigPeak
  dsimp only
  set top : 𝕋 × 𝕋 := if cosine then ((zero : 𝕋), (zero : 𝕋)) else
    (half (step_trigPiDown (𝕋 := 𝕋)), half (step_trigPiUp (𝕋 := 𝕋))) with htopdef
  -- the top first
  have htop : toReal top.1 ≤ π / 2 - aux_shift cosine ∧
      π / 2 - aux_shift cosine ≤ toReal top.2 := by
    rw [htopdef]
    cases cosine
    · simp only [Bool.false_eq_true, if_false, aux_shift, sub_zero, toReal_half]
      constructor <;> linarith
    · simp [aux_shift, toReal_zero]
  cases bottom
  · simpa using htop
  · simp only [if_true]
    have h1 := addDown_le_add top.1 step_trigPiDown
    have h2 := add_le_addUp top.2 step_trigPiUp
    exact ⟨by linarith [htop.1], by linarith [htop.2]⟩

/-- A point `A + 2π k` of `[l, u]`, `A` in the bracket, makes the test find an integer. -/
private theorem aux_inside {w aLo aHi l u : 𝕋} (hw : 0 ≤ toReal w) {A : ℝ}
    (haL : toReal aLo ≤ A) (haH : A ≤ toReal aHi) (k : ℤ) (h1 : toReal l ≤ A + 2 * π * k)
    (h2 : A + 2 * π * k ≤ toReal u) : -- --- CONCL ---
    step_trigInside w aLo aHi l u = true := by -- --- PROOF ---
  obtain ⟨hpL, hpU⟩ := aux_pi (𝕋 := 𝕋)
  have hπ := pi_pos
  unfold step_trigInside
  dsimp only
  set pL := step_trigPiDown (𝕋 := 𝕋)
  set pU := step_trigPiUp (𝕋 := 𝕋)
  set invLo := divDown one (addUp pU pU)
  set invHi := if ltStrict zero (addDown pL pL) then divUp one (addDown pL pL) else one
  -- `1 / 2π` between the two
  have hz : 0 < 1 / (2 * π) := by positivity
  have hLo : toReal invLo ≤ 1 / (2 * π) := by
    have h := add_le_addUp pU pU
    have hd := divDown_le_div one (addUp pU pU) (by linarith)
    rw [toReal_one] at hd
    exact le_trans hd (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hHi : 1 / (2 * π) ≤ toReal invHi := by
    simp only [invHi]
    split_ifs with h
    · have hp := toReal_lt_of_ltStrict h
      rw [toReal_zero] at hp
      have hd := addDown_le_add pL pL
      have hu := div_le_divUp one (addDown pL pL) hp
      rw [toReal_one] at hu
      exact le_trans (one_div_le_one_div_of_le hp (by linarith)) hu
    · rw [toReal_one, div_le_one (by positivity)]; linarith [pi_gt_three]
  -- a product with a factor between `invLo` and `invHi`, both ways
  have hmin : ∀ a : 𝕋, toReal (minimum (mulDown a invLo) (mulDown a invHi))
      ≤ toReal a * (1 / (2 * π)) := by
    intro a
    rw [toReal_minimum]
    have h1 := mulDown_le_mul a invLo
    have h2 := mulDown_le_mul a invHi
    rcases le_total 0 (toReal a) with ha | ha
    · exact le_trans (min_le_left _ _) (le_trans h1 (mul_le_mul_of_nonneg_left hLo ha))
    · exact le_trans (min_le_right _ _) (le_trans h2 (mul_le_mul_of_nonpos_left hHi ha))
  have hmax : ∀ a : 𝕋, toReal a * (1 / (2 * π))
      ≤ toReal (maximum (mulUp a invLo) (mulUp a invHi)) := by
    intro a
    rw [toReal_maximum]
    have h1 := mul_le_mulUp a invLo
    have h2 := mul_le_mulUp a invHi
    rcases le_total 0 (toReal a) with ha | ha
    · exact le_trans (mul_le_mul_of_nonneg_left hHi ha) (le_trans h2 (le_max_right _ _))
    · exact le_trans (mul_le_mul_of_nonpos_left hLo ha) (le_trans h1 (le_max_left _ _))
  -- the widening is not negative
  have hwid : ∀ a : 𝕋, 0 ≤ toReal (mulUp (addUp (absolute a) one) w) := by
    intro a
    have h1 := add_le_addUp (absolute a) one
    rw [toReal_absolute, toReal_one] at h1
    have h3 := mul_le_mulUp (addUp (absolute a) one) w
    nlinarith [abs_nonneg (toReal a)]
  -- the lower quotient is at most `k`, the upper at least `k`
  set tl := minimum (mulDown (subDown l aHi) invLo) (mulDown (subDown l aHi) invHi)
  set tu := maximum (mulUp (subUp u aLo) invLo) (mulUp (subUp u aLo) invHi)
  have hsl : toReal (subDown tl (mulUp (addUp (absolute tl) one) w)) ≤ k := by
    have h3 := subDown_le_sub tl (mulUp (addUp (absolute tl) one) w)
    have h4 := hmin (subDown l aHi)
    have h5 := subDown_le_sub l aHi
    have h6 : (toReal l - A) * (1 / (2 * π)) ≤ k := by
      rw [← div_eq_mul_one_div, div_le_iff₀ (by positivity)]; linarith
    have h7 := mul_le_mul_of_nonneg_right (by linarith : toReal (subDown l aHi) ≤ toReal l - A)
      hz.le
    linarith [hwid tl]
  -- the upper one, the same way
  have hsu : (k : ℝ) ≤ toReal (addUp tu (mulUp (addUp (absolute tu) one) w)) := by
    have h3 := add_le_addUp tu (mulUp (addUp (absolute tu) one) w)
    have h4 := hmax (subUp u aLo)
    have h5 := sub_le_subUp u aLo
    have h6 : (k : ℝ) ≤ (toReal u - A) * (1 / (2 * π)) := by
      rw [← div_eq_mul_one_div, le_div_iff₀ (by positivity)]; linarith
    have h7 := mul_le_mul_of_nonneg_right (by linarith : toReal u - A ≤ toReal (subUp u aLo))
      hz.le
    linarith [hwid tu]
  -- so an integer lies between them
  have hc : ⌈ToRat.toRat (subDown tl (mulUp (addUp (absolute tl) one) w))⌉ ≤ k := by
    rw [Int.ceil_le]
    have := ToRat.toReal_toRat (subDown tl (mulUp (addUp (absolute tl) one) w))
    exact_mod_cast (this ▸ hsl : ((ToRat.toRat (subDown tl (mulUp (addUp (absolute tl) one) w))
      : ℚ) : ℝ) ≤ (k : ℝ))
  have hf : k ≤ ⌊ToRat.toRat (addUp tu (mulUp (addUp (absolute tu) one) w))⌋ := by
    rw [Int.le_floor]
    have := ToRat.toReal_toRat (addUp tu (mulUp (addUp (absolute tu) one) w))
    exact_mod_cast (this ▸ hsu : (k : ℝ) ≤ ((ToRat.toRat (addUp tu (mulUp (addUp (absolute tu)
      one) w)) : ℚ) : ℝ))
  exact if_pos (le_trans hc hf)

/-- The box: `f` on `[l, u]` lies between its two ends. -/
private theorem aux_box (cosine : Bool) (n : ℕ) {w : 𝕋} (hw : 0 ≤ toReal w) {l u : 𝕋} {t : ℝ}
    (hl : toReal l ≤ t) (hu : t ≤ toReal u) : -- --- CONCL ---
    toReal (step_trigBoxLo cosine n w l u) ≤ sin (t + aux_shift cosine) ∧
      sin (t + aux_shift cosine) ≤ toReal (step_trigBoxHi cosine n w l u) := by -- --- PROOF ---
  set δ := aux_shift cosine
  -- the end values, both ways
  have hD : ∀ x : 𝕋, toReal (if cosine then cosDown n x else sinDown n x) ≤ sin (toReal x + δ) :=
    fun x => by
      rw [← aux_f]; cases cosine
      · exact sinDown_le n x
      · exact cosDown_le n x
  have hU : ∀ x : 𝕋, sin (toReal x + δ) ≤ toReal (if cosine then cosUp n x else sinUp n x) :=
    fun x => by
      rw [← aux_f]; cases cosine
      · exact le_sinUp n x
      · exact le_cosUp n x
  constructor
  · unfold step_trigBoxLo
    dsimp only
    by_cases hin : step_trigInside w (step_trigPeak (𝕋 := 𝕋) cosine true).1
      (step_trigPeak (𝕋 := 𝕋) cosine true).2 l u = true
    · rw [if_pos hin, toReal_neg, toReal_one]; exact neg_one_le_sin _
    · rw [if_neg hin]
      -- no trough: at least the smaller end
      have hno : ∀ k : ℤ, ¬ (toReal l ≤ -(π / 2) - δ + 2 * π * k ∧
          -(π / 2) - δ + 2 * π * k ≤ toReal u) := by
        rintro k ⟨h1, h2⟩
        obtain ⟨hb1, hb2⟩ := aux_peak (𝕋 := 𝕋) cosine true
        simp only [if_true] at hb1 hb2
        exact hin (aux_inside hw hb1 hb2 (k - 1) (by push_cast; linarith)
          (by push_cast; linarith))
      have hm := aux_no_trough hno hl hu
      -- the smaller end value from below, less `w`
      rw [toReal_maximum, toReal_neg, toReal_one]
      refine max_le ?_ (neg_one_le_sin _)
      have h1 := subDown_le_sub (minimum (if cosine then cosDown n l else sinDown n l)
        (if cosine then cosDown n u else sinDown n u)) w
      rw [toReal_minimum] at h1
      have h2 := min_le_min (hD l) (hD u)
      linarith
  · unfold step_trigBoxHi
    dsimp only
    by_cases hin : step_trigInside w (step_trigPeak (𝕋 := 𝕋) cosine false).1
      (step_trigPeak (𝕋 := 𝕋) cosine false).2 l u = true
    · rw [if_pos hin, toReal_one]; exact sin_le_one _
    · rw [if_neg hin]
      -- no peak: at most the larger end
      have hno : ∀ k : ℤ, ¬ (toReal l ≤ π / 2 - δ + 2 * π * k ∧
          π / 2 - δ + 2 * π * k ≤ toReal u) := by
        rintro k ⟨h1, h2⟩
        obtain ⟨hb1, hb2⟩ := aux_peak (𝕋 := 𝕋) cosine false
        simp only [Bool.false_eq_true, if_false, add_zero] at hb1 hb2
        exact hin (aux_inside hw hb1 hb2 k h1 h2)
      have hm := aux_no_peak hno hl hu
      rw [toReal_minimum, toReal_one]
      refine le_min ?_ (sin_le_one _)
      have h1 := add_le_addUp (maximum (if cosine then cosUp n l else sinUp n l)
        (if cosine then cosUp n u else sinUp n u)) w
      rw [toReal_maximum] at h1
      have h2 := max_le_max (hU l) (hU u)
      linarith

omit [ToRat 𝕋] in
/-- The reach is at least the distance to the middle. -/
private theorem aux_reach {w₄ : 𝕋} (hw₄ : 0 ≤ toReal w₄) {l u : 𝕋} {t : ℝ} (hl : toReal l ≤ t)
    (hu : t ≤ toReal u) : -- --- CONCL ---
    |t - toReal (step_trigMid l u)| ≤ toReal (step_trigReach w₄ l u) := by -- --- PROOF ---
  unfold step_trigReach
  dsimp only
  set c := step_trigMid l u
  have h1 := sub_le_subUp u c
  have h2 := sub_le_subUp c l
  have h3 := add_le_addUp one w₄
  rw [toReal_one] at h3
  have h4 := mul_le_mulUp (maximum (subUp u c) (subUp c l)) (addUp one w₄)
  have hM : |t - toReal c| ≤ toReal (maximum (subUp u c) (subUp c l)) := by
    rw [toReal_maximum, abs_le]
    constructor
    · linarith [le_max_right (toReal (subUp u c)) (toReal (subUp c l))]
    · linarith [le_max_left (toReal (subUp u c)) (toReal (subUp c l))]
  have hM0 := le_trans (abs_nonneg _) hM
  have h5 := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ toReal (addUp one w₄)) hM0
  linarith

omit [ToRat 𝕋] in
/-- The tangent's radius is at least `d² / 2`. -/
private theorem aux_radius (cosine : Bool) (n : ℕ) {w w₄ : 𝕋} (hw : 0 ≤ toReal w)
    {l u : 𝕋} (hd0 : 0 ≤ toReal (step_trigReach w₄ l u)) : -- --- CONCL ---
    toReal (step_trigReach w₄ l u) ^ 2 / 2 ≤ toReal (step_trigRadius
      cosine n w w₄ l u) := by -- --- PROOF ---
  unfold step_trigRadius
  dsimp only
  set d := step_trigReach w₄ l u
  set m := (step_trigSlope cosine n (step_trigMid l u)).1
  set k := mulUp (absolute m) (maximum (absolute l) (absolute u))
  have hb3 := mul_le_mulUp (absolute m) (maximum (absolute l) (absolute u))
  have hb4 : 0 ≤ toReal (absolute m) * toReal (maximum (absolute l) (absolute u)) := by
    rw [toReal_absolute, toReal_maximum, toReal_absolute, toReal_absolute]
    exact mul_nonneg (abs_nonneg _) (le_trans (abs_nonneg _) (le_max_left _ _))
  -- the margin's factor `1 + |m| max(|l|, |u|) + d` is not negative
  have hb1 := add_le_addUp one k
  have hb2 := add_le_addUp (addUp one k) d
  rw [toReal_one] at hb1
  have hbig : 0 ≤ toReal (addUp (addUp one k) d) := by linarith [hd0]
  have hbw := mul_le_mulUp (addUp (addUp one k) d) w
  have hbw0 := mul_nonneg hbig hw
  have hdd := mul_le_mulUp d d
  have hsum := add_le_addUp (half (mulUp d d)) (mulUp (addUp (addUp one k) d) w)
  rw [toReal_half] at hsum
  have hsq : toReal d ^ 2 = toReal d * toReal d := sq _
  linarith

omit [ToRat 𝕋] in
/-- The tangent's error is at least the radius plus the three rounding costs. -/
private theorem aux_error_sum {r e₁ e₂ e₃ d : 𝕋} :
    toReal r + toReal e₁ + toReal (mulUp e₂ d) + toReal e₃
      ≤ toReal (addUp (addUp (addUp r e₁) (mulUp e₂ d)) e₃) := by
  have k1 := add_le_addUp r e₁
  have k2 := add_le_addUp (addUp r e₁) (mulUp e₂ d)
  have k3 := add_le_addUp (addUp (addUp r e₁) (mulUp e₂ d)) e₃
  linarith

omit [ToRat 𝕋] in
/-- The value and the slope at the middle, bracketed. -/
private theorem aux_brackets (cosine : Bool) (n : ℕ) (c : 𝕋) : -- --- CONCL ---
    (toReal (step_trigValue cosine n c).1 ≤ sin (toReal c + aux_shift cosine) ∧
      sin (toReal c + aux_shift cosine) ≤ toReal (step_trigValue cosine n c).2) ∧
    (toReal (step_trigSlope cosine n c).1 ≤ cos (toReal c + aux_shift cosine) ∧
      cos (toReal c + aux_shift cosine) ≤ toReal (step_trigSlope
        cosine n c).2) := by -- --- PROOF ---
  cases cosine
  · simp only [step_trigValue, step_trigSlope, aux_shift, Bool.false_eq_true, if_false, add_zero]
    exact ⟨⟨sinDown_le n c, le_sinUp n c⟩, ⟨cosDown_le n c, le_cosUp n c⟩⟩
  · simp only [step_trigValue, step_trigSlope, aux_shift, if_true, sin_add_pi_div_two,
      cos_add_pi_div_two, toReal_neg]
    exact ⟨⟨cosDown_le n c, le_cosUp n c⟩,
      ⟨neg_le_neg (le_sinUp n c), neg_le_neg (sinDown_le n c)⟩⟩

omit [ToRat 𝕋] in
/-- The tangent at the middle, with the roundings' cost. -/
private theorem aux_tangent (cosine : Bool) (n : ℕ) {w w₄ : 𝕋} (hw : 0 ≤ toReal w)
    (hw₄ : 0 ≤ toReal w₄) {l u : 𝕋} {t : ℝ} (hl : toReal l ≤ t)
    (hu : t ≤ toReal u) : -- --- CONCL ---
    |sin (t + aux_shift cosine) - (toReal (step_trigSlope cosine n (step_trigMid l u)).1 * t
      + toReal (step_trigOffset cosine n l u))| ≤ toReal
        (step_trigError cosine n w w₄ l u) := by -- --- PROOF ---
  have hd := aux_reach hw₄ hl hu
  have hd0 : 0 ≤ toReal (step_trigReach w₄ l u) := le_trans (abs_nonneg _) hd
  have hr := aux_radius cosine n hw hd0
  have hE := aux_error_sum (r := step_trigRadius cosine n w w₄ l u)
    (e₁ := subUp (step_trigValue cosine n (step_trigMid l u)).2
      (step_trigValue cosine n (step_trigMid l u)).1)
    (e₂ := subUp (step_trigSlope cosine n (step_trigMid l u)).2
      (step_trigSlope cosine n (step_trigMid l u)).1)
    (e₃ := subUp (subUp (step_trigValue cosine n (step_trigMid l u)).1
      (mulDown (step_trigSlope cosine n (step_trigMid l u)).1 (step_trigMid l u)))
      (step_trigOffset cosine n l u))
    (d := step_trigReach w₄ l u)
  -- the error and the offset unfolded, then the middle's values as plain floats
  have hErr : step_trigError cosine n w w₄ l u = addUp (addUp (addUp
      (step_trigRadius cosine n w w₄ l u) (subUp (step_trigValue cosine n (step_trigMid l u)).2
      (step_trigValue cosine n (step_trigMid l u)).1)) (mulUp (subUp (step_trigSlope cosine n
      (step_trigMid l u)).2 (step_trigSlope cosine n (step_trigMid l u)).1)
      (step_trigReach w₄ l u))) (subUp (subUp (step_trigValue cosine n (step_trigMid l u)).1
      (mulDown (step_trigSlope cosine n (step_trigMid l u)).1 (step_trigMid l u)))
      (step_trigOffset cosine n l u)) := rfl
  have hoo : step_trigOffset cosine n l u = subDown (step_trigValue cosine n (step_trigMid l u)).1
      (mulUp (step_trigSlope cosine n (step_trigMid l u)).1 (step_trigMid l u)) := rfl
  rw [hErr, hoo]
  rw [hoo] at hE
  obtain ⟨hv, hs⟩ := aux_brackets cosine n (step_trigMid l u)
  generalize step_trigValue cosine n (step_trigMid l u) = fc at *
  generalize step_trigSlope cosine n (step_trigMid l u) = m at *
  generalize step_trigMid l u = c at *
  generalize step_trigReach w₄ l u = d at *
  set δ := aux_shift cosine
  set o := subDown fc.1 (mulUp m.1 c)
  -- the offset, both ways, and the error's parts
  have ho1 := subDown_le_sub fc.1 (mulUp m.1 c)
  have ho2 := mul_le_mulUp m.1 c
  have ho3 := sub_le_subUp fc.1 (mulDown m.1 c)
  have ho4 := mulDown_le_mul m.1 c
  have ho5 := sub_le_subUp (subUp fc.1 (mulDown m.1 c)) o
  have he₁ := sub_le_subUp fc.2 fc.1
  have he₂ := sub_le_subUp m.2 m.1
  have he₂0 : 0 ≤ toReal (subUp m.2 m.1) := by linarith [hs.1, hs.2]
  have hmd := mul_le_mulUp (subUp m.2 m.1) d
  -- Taylor, and the slope's error over the reach
  have htay := aux_taylor δ (toReal c) t
  have hsq : (t - toReal c) ^ 2 ≤ toReal d ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  have hprod : |(cos (toReal c + δ) - toReal m.1) * (t - toReal c)|
      ≤ toReal (subUp m.2 m.1) * toReal d := by
    rw [abs_mul, abs_of_nonneg (by linarith [hs.1])]
    exact mul_le_mul (by linarith [hs.2]) hd (abs_nonneg _) he₂0
  -- the four parts
  have hid : sin (t + δ) - (toReal m.1 * t + toReal o)
      = (sin (t + δ) - (sin (toReal c + δ) + cos (toReal c + δ) * (t - toReal c)))
        + (sin (toReal c + δ) - toReal fc.1)
        + (cos (toReal c + δ) - toReal m.1) * (t - toReal c)
        + (toReal fc.1 - toReal m.1 * toReal c - toReal o) := by ring
  rw [hid]
  rw [abs_le] at htay hprod ⊢
  constructor <;> linarith [hv.1, hv.2]


-- =======================================  MAIN THEOREM  ======================================= --

theorem trigRelaxation_encloses (cosine : Bool) (n : ℕ) {w w₁ w₄ : 𝕋} (hw : 0 ≤ toReal w)
    (hw₁ : 0 ≤ toReal w₁) (hw₄ : 0 ≤ toReal w₄) : -- --- CONCL ---
    (trigRelaxation cosine n w w₁ w₄).Encloses fun x => if cosine
      then cos x else sin x := by -- --- PROOF ---
  -- the band over the box
  have hB : (step_trigBand cosine n w w₁).EnclosesWhere (fun x => if cosine then cos x else sin x)
      fun _ _ => True := Relaxation.ofBand_enclosesWhere (fun {l u t} _ hl hu => by
        rw [toReal_zero, zero_mul, sub_zero, aux_f]
        exact aux_box cosine n hw hl hu) (fun {l u} _ => by
        -- the margin `w₁ (|hi| + |lo|)` is not negative
        have h1 := add_le_addUp (absolute (step_trigBoxHi cosine n w l u))
          (absolute (step_trigBoxLo cosine n w l u))
        rw [toReal_absolute, toReal_absolute] at h1
        have h2 := mul_le_mulUp (addUp (absolute (step_trigBoxHi cosine n w l u))
          (absolute (step_trigBoxLo cosine n w l u))) w₁
        have h0 : 0 ≤ toReal (addUp (absolute (step_trigBoxHi cosine n w l u))
          (absolute (step_trigBoxLo cosine n w l u))) := by
          linarith [abs_nonneg (toReal (step_trigBoxHi cosine n w l u)),
            abs_nonneg (toReal (step_trigBoxLo cosine n w l u))]
        exact le_trans (mul_nonneg h0 hw₁) h2)
  -- whichever line the relaxation takes
  refine ⟨fun {l u t} hl hu => ?_⟩
  by_cases huse : step_trigUse cosine n w w₁ w₄ l u = true
  · simp only [trigRelaxation, if_pos huse]
    rw [aux_f]
    exact aux_tangent cosine n hw hw₄ hl hu
  · simp only [trigRelaxation, if_neg huse]
    exact hB.sound trivial hl hu

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
