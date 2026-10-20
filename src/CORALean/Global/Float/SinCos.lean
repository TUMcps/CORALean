module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.Global.Float.PowUp
public import CORALean.Global.Float.DivFact
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# Sine and cosine rounded in either direction

`sinDown`/`sinUp` and `cosDown`/`cosUp` enclose `Real.sin` and `Real.cos` at a float, out of
`FloatOps` alone, at every argument and precision `n`. Argument reduction is by halving, as for
`expUp`: at the exact `y = a / 2ⁿ` both are enclosed by Mathlib's Taylor bounds for `|y| ≤ 1`
(`|sin y - (y - y³/6)| ≤ |y|⁵/100`, `1 - y²/2 ≤ cos y ≤ 1 - y²/2 + 5y⁴/96`), and the `n` doublings
back are interval arithmetic on the pair, every bound clamped to `[-1, 1]`. Nothing is assumed of
the argument: where `le` (certifying `true` only) cannot place `y` in `[-1, 1]` or decide its
sign, the seed and the result are the trivial `[-1, 1]`, sound and as coarse as it says.

## Inputs
* `n` – number of halvings
* `a` – float argument

## Hypotheses
* none

## Conclusion
* the downward sine bound is at most the sine
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]

namespace SinCos

/-- `a / 2 ^ n`, exactly. -/
def halfIter : ℕ → 𝕋 → 𝕋
  | 0, a => a
  | k + 1, a => half (halfIter k a)

/-- The least corner product of `[a, b]` and `[c, d]`, each rounded down. -/
def cornerLo (a b c d : 𝕋) : 𝕋 :=
  minimum (minimum (mulDown a c) (mulDown a d)) (minimum (mulDown b c) (mulDown b d))

/-- The greatest corner product, each rounded up. -/
def cornerHi (a b c d : 𝕋) : 𝕋 :=
  maximum (maximum (mulUp a c) (mulUp a d)) (maximum (mulUp b c) (mulUp b d))

/-- Into `[-1, 1]`, where both functions live: harmless to a bound on either side. -/
def clampUnit (a : 𝕋) : 𝕋 := maximum (neg one) (minimum one a)

/-- `sin` and `cos` at one angle, each between two floats. -/
structure SinCosBox (𝕋 : Type) where
  sl : 𝕋
  su : 𝕋
  cl : 𝕋
  cu : 𝕋

/-- The trivial box, `[-1, 1]` for both. -/
def unitBox : SinCosBox 𝕋 := ⟨neg one, one, neg one, one⟩

/-- `sin t` for `0 ≤ t ≤ 1`: `t - t³/6 ± t⁵/64`. -/
def sinSeedNonneg (t : 𝕋) : Interval 𝕋 :=
  let t2 := maximum zero (mulDown t t)                              -- t² from below
  let t3 : Interval 𝕋 := ⟨maximum zero (mulDown t2 t), mulUp (mulUp t t) t⟩      -- t³, both sides
  let d := divFact t3 3                                             -- t³/6, both sides
  let e := halfIter 6 (powUp t 5)                              -- t⁵/64 ≥ t⁵/100
  ⟨subDown (subDown t d.sup) e, addUp (subUp t d.inf) e⟩

/-- `cos t` for `0 ≤ t ≤ 1`: from `1 - t²/2` to `1 - t²/2 + t⁴/16`. -/
def cosSeed (t : 𝕋) : Interval 𝕋 :=
  let t2l := maximum zero (mulDown t t)
  let t2u := mulUp t t
  let e := halfIter 4 (powUp t 4)                              -- t⁴/16 ≥ 5t⁴/96
  ⟨subDown one (half t2u), addUp (subUp one (half t2l)) e⟩

/-- Both at `y`, for `|y| ≤ 1` certified; the sine by oddness below zero. -/
def seed (y : 𝕋) : SinCosBox 𝕋 :=
  let t := absolute y
  if le t one = true then
    let s := if le zero y = true then sinSeedNonneg y
      else if le y zero = true then
        ⟨neg (sinSeedNonneg (neg y)).sup, neg (sinSeedNonneg (neg y)).inf⟩
      else ⟨neg one, one⟩
    let c := cosSeed t
    ⟨s.inf, s.sup, c.inf, c.sup⟩
  else unitBox

/-- From `θ` to `2θ`. -/
def double (B : SinCosBox 𝕋) : SinCosBox 𝕋 :=
  let pl := cornerLo B.sl B.su B.cl B.cu                    -- sin θ cos θ
  let pu := cornerHi B.sl B.su B.cl B.cu
  let ql := maximum zero (cornerLo B.sl B.su B.sl B.su)     -- sin² θ
  let qu := cornerHi B.sl B.su B.sl B.su
  let rl := maximum zero (cornerLo B.cl B.cu B.cl B.cu)     -- cos² θ
  let ru := cornerHi B.cl B.cu B.cl B.cu
  ⟨clampUnit (addDown pl pl), clampUnit (addUp pu pu),
    clampUnit (maximum (subDown one (addUp qu qu)) (subDown (addDown rl rl) one)),
    clampUnit (minimum (subUp one (addDown ql ql)) (subUp (addUp ru ru) one))⟩

def doubleIter : ℕ → SinCosBox 𝕋 → SinCosBox 𝕋
  | 0, B => B
  | k + 1, B => doubleIter k (double B)

/-- Seed at `a / 2ⁿ`, then double `n` times. -/
def sinCosBox (n : ℕ) (a : 𝕋) : SinCosBox 𝕋 := doubleIter n (seed (halfIter n a))

end SinCos

open SinCos

/-- `sin a` from below, at every `a`; `n` is the number of halvings. -/
def sinDown (n : ℕ) (a : 𝕋) : 𝕋 := clampUnit (sinCosBox n a).sl

/-- `sin a` from above, at every `a`. -/
def sinUp (n : ℕ) (a : 𝕋) : 𝕋 := clampUnit (sinCosBox n a).su

/-- `cos a` from below, at every `a`. -/
def cosDown (n : ℕ) (a : 𝕋) : 𝕋 := clampUnit (sinCosBox n a).cl

/-- `cos a` from above, at every `a`. -/
def cosUp (n : ℕ) (a : 𝕋) : 𝕋 := clampUnit (sinCosBox n a).cu

open SoundFloatArithmetic

variable [SoundFloatArithmetic 𝕋]

/-- What a box claims of an angle. -/
private def Holds (θ : ℝ) (B : SinCosBox 𝕋) : Prop :=
  toReal B.sl ≤ Real.sin θ ∧ Real.sin θ ≤ toReal B.su ∧
    toReal B.cl ≤ Real.cos θ ∧ Real.cos θ ≤ toReal B.cu

private theorem toReal_halfIter (n : ℕ) (a : 𝕋) : -- --- CONCL ---
    toReal (halfIter n a) = toReal a / 2 ^ n := by -- --- PROOF ---
  induction n with
  | zero => rw [halfIter, pow_zero, div_one]
  | succ k ih =>
    rw [halfIter, toReal_half, ih, pow_succ]
    ring

/-- `k x` lies between its values at the ends of `[c, d]`. -/
private theorem mul_between {k c d x : ℝ} (h1 : c ≤ x) (h2 : x ≤ d) : -- --- CONCL ---
    min (k * c) (k * d) ≤ k * x ∧ k * x ≤ max (k * c) (k * d) := by -- --- PROOF ---
  rcases le_total 0 k with hk | hk
  · exact ⟨min_le_of_left_le (mul_le_mul_of_nonneg_left h1 hk),
      le_max_of_le_right (mul_le_mul_of_nonneg_left h2 hk)⟩
  · exact ⟨min_le_of_right_le (mul_le_mul_of_nonpos_left h2 hk),
      le_max_of_le_left (mul_le_mul_of_nonpos_left h1 hk)⟩

/-- A product of two bounded factors stays between the four corners. -/
private theorem corner_bounds {a b c d : 𝕋} {y x : ℝ} (hy1 : toReal a ≤ y) (hy2 : y ≤ toReal b)
    (hx1 : toReal c ≤ x) (hx2 : x ≤ toReal d) : -- --- CONCL ---
    toReal (cornerLo a b c d) ≤ y * x ∧ y * x ≤ toReal (cornerHi a b c d) := by -- --- PROOF ---
  have hy := mul_between (k := x) hy1 hy2
  have ha := mul_between (k := toReal a) hx1 hx2
  have hb := mul_between (k := toReal b) hx1 hx2
  rw [mul_comm x, mul_comm x, mul_comm x] at hy
  -- the four corners, rounded each way
  have e1 := mulDown_le_mul a c
  have e2 := mulDown_le_mul a d
  have e3 := mulDown_le_mul b c
  have e4 := mulDown_le_mul b d
  have f1 := mul_le_mulUp a c
  have f2 := mul_le_mulUp a d
  have f3 := mul_le_mulUp b c
  have f4 := mul_le_mulUp b d
  simp only [cornerLo, cornerHi, toReal_minimum, toReal_maximum]
  -- linear in `y` first, then in `x` at each end of `y`'s range
  constructor
  · refine le_trans ?_ hy.1
    refine le_min ?_ ?_
    · exact le_trans (min_le_min (min_le_min e1 e2) (min_le_min e3 e4))
        (le_trans (min_le_left _ _) ha.1)
    · exact le_trans (min_le_min (min_le_min e1 e2) (min_le_min e3 e4))
        (le_trans (min_le_right _ _) hb.1)
  · refine le_trans hy.2 ?_
    refine max_le ?_ ?_
    · exact le_trans (le_trans ha.2 (le_max_left _ _))
        (max_le_max (max_le_max f1 f2) (max_le_max f3 f4))
    · exact le_trans (le_trans hb.2 (le_max_right _ _))
        (max_le_max (max_le_max f1 f2) (max_le_max f3 f4))

/-- Clamping keeps a lower bound of a value in `[-1, 1]`. -/
private theorem clampUnit_le {a : 𝕋} {v : ℝ} (h : toReal a ≤ v) (h1 : -1 ≤ v) (_h2 : v ≤ 1) :
    toReal (clampUnit a) ≤ v := by
  rw [clampUnit, toReal_maximum, toReal_minimum, toReal_neg, toReal_one]
  exact max_le h1 (le_trans (min_le_right _ _) h)

/-- And an upper bound. -/
private theorem le_clampUnit {a : 𝕋} {v : ℝ} (h : v ≤ toReal a) (_h1 : -1 ≤ v) (h2 : v ≤ 1) :
    v ≤ toReal (clampUnit a) := by
  rw [clampUnit, toReal_maximum, toReal_minimum, toReal_neg, toReal_one]
  exact le_max_of_le_right (le_min h2 h)

/-- The trivial box holds at every angle. -/
private theorem unitBox_holds (θ : ℝ) : Holds θ (unitBox : SinCosBox 𝕋) := by
  simp only [Holds, unitBox, toReal_neg, toReal_one]
  exact ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ, Real.neg_one_le_cos θ, Real.cos_le_one θ⟩

/-- The sine seed: `Real.sin_bound`, each of its roundings paid. -/
private theorem sinSeedNonneg_mem {t : 𝕋} (h0 : 0 ≤ toReal t) (h1 : toReal t ≤ 1) : -- --- CONCL ---
    toReal (sinSeedNonneg t).inf ≤ Real.sin (toReal t) ∧
      Real.sin (toReal t) ≤ toReal (sinSeedNonneg t).sup := by -- --- PROOF ---
  set x := toReal t
  have hb := Real.sin_bound (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0, abs_le] at hb
  -- `t³` from both sides, then divided by `3! = 6`
  have hm := mulDown_le_mul t t
  have h2 : toReal (maximum zero (mulDown t t)) ≤ x * x := by
    rw [toReal_maximum, toReal_zero]; exact max_le (mul_nonneg h0 h0) hm
  have h2' : 0 ≤ toReal (maximum zero (mulDown t t)) := by
    rw [toReal_maximum, toReal_zero]; exact le_max_left _ _
  have h3l : toReal (maximum zero (mulDown (maximum zero (mulDown t t)) t)) ≤ x ^ 3 := by
    rw [toReal_maximum, toReal_zero]
    refine max_le (by positivity) (le_trans (mulDown_le_mul _ _) ?_)
    rw [pow_succ, sq]; exact mul_le_mul_of_nonneg_right h2 h0
  have h3u : x ^ 3 ≤ toReal (mulUp (mulUp t t) t) := by
    refine le_trans ?_ (mul_le_mulUp _ _)
    rw [pow_succ, sq]; exact mul_le_mul_of_nonneg_right (mul_le_mulUp t t) h0
  have hd := divFact_mem ⟨maximum zero (mulDown (maximum zero (mulDown t t)) t),
    mulUp (mulUp t t) t⟩ (pow_nonneg h0 3) ⟨h3l, h3u⟩ 3
  -- `3! = 6`
  have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6] at hd
  -- `t⁵ / 64`, which bounds `t⁵ / 100`
  have he : x ^ 5 / 100 ≤ toReal (halfIter 6 (powUp t 5)) := by
    rw [toReal_halfIter]
    have := le_powUp (B := t) h0 le_rfl 5
    have h5 : 0 ≤ x ^ 5 := pow_nonneg h0 5
    linarith
  -- the two ends, `t - t³/6 ∓ t⁵/64`
  simp only [sinSeedNonneg]
  constructor
  · refine le_trans (subDown_le_sub _ _) ?_
    have := subDown_le_sub t (divFact ⟨maximum zero (mulDown (maximum zero (mulDown t t)) t),
      mulUp (mulUp t t) t⟩ 3).sup
    linarith [hd.2]
  · refine le_trans ?_ (add_le_addUp _ _)
    have := sub_le_subUp t (divFact ⟨maximum zero (mulDown (maximum zero (mulDown t t)) t),
      mulUp (mulUp t t) t⟩ 3).inf
    linarith [hd.1]

/-- The cosine seed: `one_sub_sq_div_two_le_cos` below, `Real.cos_bound` above. -/
private theorem cosSeed_mem {t : 𝕋} (h0 : 0 ≤ toReal t) (h1 : toReal t ≤ 1) : -- --- CONCL ---
    toReal (cosSeed t).inf ≤ Real.cos (toReal t) ∧
      Real.cos (toReal t) ≤ toReal (cosSeed t).sup := by -- --- PROOF ---
  set x := toReal t
  have hb := Real.cos_bound (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0, abs_le] at hb
  have hl := Real.one_sub_sq_div_two_le_cos (x := x)
  have hu := mul_le_mulUp t t
  have hm : toReal (maximum zero (mulDown t t)) ≤ x * x := by
    rw [toReal_maximum, toReal_zero]; exact max_le (mul_nonneg h0 h0) (mulDown_le_mul t t)
  have he : x ^ 4 * (5 / 96) ≤ toReal (halfIter 4 (powUp t 4)) := by
    rw [toReal_halfIter]
    have := le_powUp (B := t) h0 le_rfl 4
    have h4 : 0 ≤ x ^ 4 := pow_nonneg h0 4
    linarith
  have hsq : x ^ 2 = x * x := sq x
  -- the two ends, `1 - t²/2` and `1 - t²/2 + t⁴/16`
  simp only [cosSeed]
  constructor
  · refine le_trans (subDown_le_sub _ _) ?_
    rw [toReal_one, toReal_half]
    linarith
  · refine le_trans ?_ (add_le_addUp _ _)
    have := sub_le_subUp (one : 𝕋) (half (maximum zero (mulDown t t)))
    rw [toReal_one, toReal_half] at this
    linarith

private theorem seed_holds (y : 𝕋) : -- --- CONCL ---
    Holds (toReal y) (seed y) := by -- --- PROOF ---
  by_cases ht : le (absolute y) one = true
  · have hy := toReal_le_of_le ht
    rw [toReal_absolute, toReal_one] at hy
    have hc := cosSeed_mem (t := absolute y) (by rw [toReal_absolute]; exact abs_nonneg _)
      (by rw [toReal_absolute]; exact hy)
    rw [toReal_absolute, Real.cos_abs] at hc
    -- the sign of `y` decided by `le`, the sine by oddness below zero
    by_cases hz : le zero y = true
    · have h0 : 0 ≤ toReal y := by have := toReal_le_of_le hz; rwa [toReal_zero] at this
      have hs := sinSeedNonneg_mem h0 (le_trans (le_abs_self _) hy)
      simp only [seed, ht, hz, if_true]
      exact ⟨hs.1, hs.2, hc.1, hc.2⟩
    · by_cases hn : le y zero = true
      · have h0 : toReal y ≤ 0 := by have := toReal_le_of_le hn; rwa [toReal_zero] at this
        have hs := sinSeedNonneg_mem (t := neg y) (by rw [toReal_neg]; linarith)
          (by rw [toReal_neg]; linarith [neg_abs_le (toReal y)])
        rw [toReal_neg, Real.sin_neg] at hs
        simp only [seed, ht, hz, hn, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, ?_, hc.1, hc.2⟩
        · simp only [toReal_neg]; linarith [hs.2]
        · simp only [toReal_neg]; linarith [hs.1]
      · -- the sign undecided: the trivial sine bounds
        simp only [seed, ht, hz, hn, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, ?_, hc.1, hc.2⟩
        · show toReal (neg one) ≤ _
          rw [toReal_neg, toReal_one]; exact Real.neg_one_le_sin _
        · show _ ≤ toReal one
          rw [toReal_one]; exact Real.sin_le_one _
  · simp only [seed, ht, Bool.false_eq_true, ↓reduceIte]
    exact unitBox_holds _

/-- One doubling keeps the claim, at twice the angle. -/
private theorem double_holds {θ : ℝ} {B : SinCosBox 𝕋} (h : Holds θ B) : -- --- CONCL ---
    Holds (2 * θ) (double B) := by -- --- PROOF ---
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hp := corner_bounds h1 h2 h3 h4
  have hq := corner_bounds h1 h2 h1 h2
  have hr := corner_bounds h3 h4 h3 h4
  have hs2 := Real.sin_two_mul θ
  have hc2 := Real.cos_two_mul θ
  have hc2' : Real.cos (2 * θ) = 1 - 2 * Real.sin θ ^ 2 := by
    rw [Real.cos_two_mul, Real.cos_sq']; ring
  -- the three products, between their corners
  have hsq := sq (Real.sin θ)
  have hcq := sq (Real.cos θ)
  have sb := Real.neg_one_le_sin (2 * θ)
  have sb' := Real.sin_le_one (2 * θ)
  have cb := Real.neg_one_le_cos (2 * θ)
  have cb' := Real.cos_le_one (2 * θ)
  have hql : toReal (maximum zero (cornerLo B.sl B.su B.sl B.su)) ≤ Real.sin θ * Real.sin θ := by
    rw [toReal_maximum, toReal_zero]; exact max_le (mul_self_nonneg _) hq.1
  have hrl : toReal (maximum zero (cornerLo B.cl B.cu B.cl B.cu)) ≤ Real.cos θ * Real.cos θ := by
    rw [toReal_maximum, toReal_zero]; exact max_le (mul_self_nonneg _) hr.1
  -- `sin 2θ = 2 sin θ cos θ`
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine clampUnit_le (le_trans (addDown_le_add _ _) ?_) sb sb'
    linarith [hp.1]
  · refine le_clampUnit (le_trans ?_ (add_le_addUp _ _)) sb sb'
    linarith [hp.2]
  -- `cos 2θ = 1 - 2 sin²θ = 2 cos²θ - 1`, the tighter of the two
  · refine clampUnit_le ?_ cb cb'
    rw [toReal_maximum]
    refine max_le (le_trans (subDown_le_sub _ _) ?_) (le_trans (subDown_le_sub _ _) ?_)
    · have := add_le_addUp (cornerHi B.sl B.su B.sl B.su) (cornerHi B.sl B.su B.sl B.su)
      rw [toReal_one]; linarith [hq.2]
    · have := addDown_le_add (maximum zero (cornerLo B.cl B.cu B.cl B.cu))
        (maximum zero (cornerLo B.cl B.cu B.cl B.cu))
      rw [toReal_one]; linarith
  · refine le_clampUnit ?_ cb cb'
    rw [toReal_minimum]
    refine le_min (le_trans ?_ (sub_le_subUp _ _)) (le_trans ?_ (sub_le_subUp _ _))
    · have := addDown_le_add (maximum zero (cornerLo B.sl B.su B.sl B.su))
        (maximum zero (cornerLo B.sl B.su B.sl B.su))
      rw [toReal_one]; linarith
    · have := add_le_addUp (cornerHi B.cl B.cu B.cl B.cu) (cornerHi B.cl B.cu B.cl B.cu)
      rw [toReal_one]; linarith [hr.2]

private theorem doubleIter_holds (n : ℕ) {θ : ℝ} {B : SinCosBox 𝕋}
    (h : Holds θ B) : -- --- CONCL ---
    Holds (2 ^ n * θ) (doubleIter n B) := by -- --- PROOF ---
  induction n generalizing θ B with
  | zero => rw [doubleIter, pow_zero, one_mul]; exact h
  | succ k ih =>
    have hstep := ih (double_holds h)
    rw [show (2:ℝ) ^ k * (2 * θ) = 2 ^ (k + 1) * θ by rw [pow_succ]; ring] at hstep
    rw [doubleIter]
    exact hstep

private theorem sinCosBox_holds (n : ℕ) (a : 𝕋) : Holds (toReal a) (sinCosBox n a) := by
  have h := doubleIter_holds n (seed_holds (halfIter n a))
  rwa [toReal_halfIter, mul_div_cancel₀ _ (pow_ne_zero _ two_ne_zero)] at h


-- =======================================  MAIN THEOREM  ======================================= --

theorem sinDown_le (n : ℕ) (a : 𝕋) : toReal (sinDown n a) ≤ Real.sin (toReal a) :=
  clampUnit_le (sinCosBox_holds n a).1 (Real.neg_one_le_sin _) (Real.sin_le_one _)

theorem le_sinUp (n : ℕ) (a : 𝕋) : Real.sin (toReal a) ≤ toReal (sinUp n a) :=
  le_clampUnit (sinCosBox_holds n a).2.1 (Real.neg_one_le_sin _) (Real.sin_le_one _)

theorem cosDown_le (n : ℕ) (a : 𝕋) : toReal (cosDown n a) ≤ Real.cos (toReal a) :=
  clampUnit_le (sinCosBox_holds n a).2.2.1 (Real.neg_one_le_cos _) (Real.cos_le_one _)

theorem le_cosUp (n : ℕ) (a : 𝕋) : Real.cos (toReal a) ≤ toReal (cosUp n a) :=
  le_clampUnit (sinCosBox_holds n a).2.2.2 (Real.neg_one_le_cos _) (Real.cos_le_one _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
