module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.SinCos
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

/-!
# The range of sine and cosine over a float range

`cosRange n l u` and `sinRange n l u` enclose `cos x` and `sin x` for every `x ∈ [l, u]`. CORA's
`@interval/cos` locates the extremal points `kπ` by reducing the range modulo `2π`, which needs an
enclosure of `π` and a rounding to an integer, neither of which `FloatOps` has. These certify
monotonicity instead: the derivative on `[l, u]` is within `r` of its value at a float `m` near the
middle, `r ≥ |x - m|`. If it is certified of one sign the function is monotone and the range is
between its values at the ends, rounded outward; otherwise the range is the midpoint form
`f(m) ± r`, clamped to `[-1, 1]`: sound, and tight for a narrow range.

## Inputs
* `n` – number of halvings
* `l` – lower end of the range
* `u` – upper end of the range
* `x` – real point

## Hypotheses
* `h1` – the point is at least the lower end
* `h2` – the point is at most the upper end

## Conclusion
* the cosine of the point lies in the computed enclosure
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]

namespace TrigRange

/-- A float near the middle of `[l, u]`; any float would be sound. -/
def midOf (l u : 𝕋) : 𝕋 := half (addUp l u)

/-- At least the distance from `midOf l u` to any point of `[l, u]`. -/
def radOf (l u : 𝕋) : 𝕋 := maximum (subUp u (midOf l u)) (subUp (midOf l u) l)

end TrigRange

open TrigRange

/-- `cos` over `[l, u]`: falling where the sine is certified non-negative, rising where it is
certified non-positive, the midpoint form otherwise. -/
def cosRange (n : ℕ) (l u : 𝕋) : Interval 𝕋 :=
  let m := midOf l u
  let r := radOf l u
  if le zero (subDown (sinDown n m) r) = true then ⟨cosDown n u, cosUp n l⟩
  else if le (addUp (sinUp n m) r) zero = true then ⟨cosDown n l, cosUp n u⟩
  else ⟨maximum (neg one) (subDown (cosDown n m) r), minimum one (addUp (cosUp n m) r)⟩

/-- `sin` over `[l, u]`: rising where the cosine is certified non-negative, falling where it is
certified non-positive, the midpoint form otherwise. -/
def sinRange (n : ℕ) (l u : 𝕋) : Interval 𝕋 :=
  let m := midOf l u
  let r := radOf l u
  if le zero (subDown (cosDown n m) r) = true then ⟨sinDown n l, sinUp n u⟩
  else if le (addUp (cosUp n m) r) zero = true then ⟨sinDown n u, sinUp n l⟩
  else ⟨maximum (neg one) (subDown (sinDown n m) r), minimum one (addUp (sinUp n m) r)⟩

open SoundFloatArithmetic

variable [SoundFloatArithmetic 𝕋]

private theorem abs_sub_mid_le {l u : 𝕋} {x : ℝ} (h1 : toReal l ≤ x)
    (h2 : x ≤ toReal u) : -- --- CONCL ---
    |x - toReal (midOf l u)| ≤ toReal (radOf l u) := by -- --- PROOF ---
  have hu := sub_le_subUp u (midOf l u)
  have hl := sub_le_subUp (midOf l u) l
  rw [radOf, toReal_maximum, abs_le]
  constructor
  · linarith [le_max_right (toReal (subUp u (midOf l u))) (toReal (subUp (midOf l u) l))]
  · linarith [le_max_left (toReal (subUp u (midOf l u))) (toReal (subUp (midOf l u) l))]

/-- A lower bound on `g` at the middle, less the radius, bounds a 1-Lipschitz `g` on the range. -/
private theorem lip_lower {g : ℝ → ℝ} (hg : ∀ x y, |g x - g y| ≤ |x - y|) {l u : 𝕋} {b : 𝕋}
    (hb : toReal b ≤ g (toReal (midOf l u))) {x : ℝ} (h1 : toReal l ≤ x)
    (h2 : x ≤ toReal u) : -- --- CONCL ---
    toReal (subDown b (radOf l u)) ≤ g x := by -- --- PROOF ---
  have hr := abs_sub_mid_le h1 h2
  have hgx := hg x (toReal (midOf l u))
  have hs := subDown_le_sub b (radOf l u)
  rw [abs_le] at hgx
  linarith [hgx.1]

private theorem lip_upper {g : ℝ → ℝ} (hg : ∀ x y, |g x - g y| ≤ |x - y|) {l u : 𝕋} {b : 𝕋}
    (hb : g (toReal (midOf l u)) ≤ toReal b) {x : ℝ} (h1 : toReal l ≤ x)
    (h2 : x ≤ toReal u) : -- --- CONCL ---
    g x ≤ toReal (addUp b (radOf l u)) := by -- --- PROOF ---
  have hr := abs_sub_mid_le h1 h2
  have hgx := hg x (toReal (midOf l u))
  have hs := add_le_addUp b (radOf l u)
  rw [abs_le] at hgx
  linarith [hgx.2]

private theorem antitoneOn_of_nonneg {f f' : ℝ → ℝ} (hf : Continuous f)
    (hd : ∀ x, HasDerivAt f (-f' x) x) {a b : ℝ}
    (h : ∀ x, a ≤ x → x ≤ b → 0 ≤ f' x) : -- --- CONCL ---
    AntitoneOn f (Set.Icc a b) := by -- --- PROOF ---
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hf.continuousOn
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt) fun x hx => ?_
  rw [interior_Icc] at hx
  rw [(hd x).deriv]
  linarith [h x hx.1.le hx.2.le]

private theorem monotoneOn_of_nonneg {f f' : ℝ → ℝ} (hf : Continuous f)
    (hd : ∀ x, HasDerivAt f (f' x) x) {a b : ℝ}
    (h : ∀ x, a ≤ x → x ≤ b → 0 ≤ f' x) : -- --- CONCL ---
    MonotoneOn f (Set.Icc a b) := by -- --- PROOF ---
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b) hf.continuousOn
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt) fun x hx => ?_
  rw [interior_Icc] at hx
  rw [(hd x).deriv]
  exact h x hx.1.le hx.2.le

/-- The midpoint form, clamped. -/
private theorem midpoint_form {g : ℝ → ℝ} (hg : ∀ x y, |g x - g y| ≤ |x - y|)
    (hg1 : ∀ x, -1 ≤ g x ∧ g x ≤ 1) {l u lo hi : 𝕋}
    (hlo : toReal lo ≤ g (toReal (midOf l u))) (hhi : g (toReal (midOf l u)) ≤ toReal hi)
    {x : ℝ} (h1 : toReal l ≤ x) (h2 : x ≤ toReal u) : -- --- CONCL ---
    toReal (maximum (neg one) (subDown lo (radOf l u))) ≤ g x ∧
      g x ≤ toReal (minimum one (addUp hi (radOf l u))) := by -- --- PROOF ---
  rw [toReal_maximum, toReal_minimum, toReal_neg, toReal_one]
  exact ⟨max_le (hg1 x).1 (lip_lower hg hlo h1 h2),
    le_min (hg1 x).2 (lip_upper hg hhi h1 h2)⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem cosRange_mem (n : ℕ) {l u : 𝕋} {x : ℝ} (h1 : toReal l ≤ x)
    (h2 : x ≤ toReal u) : -- --- CONCL ---
    toReal (cosRange n l u).inf ≤ Real.cos x ∧
      Real.cos x ≤ toReal (cosRange n l u).sup := by -- --- PROOF ---
  have hl : toReal l ≤ toReal u := le_trans h1 h2
  have hlu : toReal l ∈ Set.Icc (toReal l) (toReal u) := ⟨le_rfl, hl⟩
  have huu : toReal u ∈ Set.Icc (toReal l) (toReal u) := ⟨hl, le_rfl⟩
  have hx : x ∈ Set.Icc (toReal l) (toReal u) := ⟨h1, h2⟩
  simp only [cosRange]
  split_ifs with hs hc
  · -- the sine non-negative on the range: the cosine falls
    have hs0 : ∀ z, toReal l ≤ z → z ≤ toReal u → 0 ≤ Real.sin z := fun z hz1 hz2 => by
      have := toReal_le_of_le hs
      rw [toReal_zero] at this
      exact le_trans this (lip_lower Real.abs_sin_sub_sin_le (sinDown_le n _) hz1 hz2)
    have ha := antitoneOn_of_nonneg Real.continuous_cos Real.hasDerivAt_cos hs0
    exact ⟨le_trans (cosDown_le n u) (ha hx huu h2), le_trans (ha hlu hx h1) (le_cosUp n l)⟩
  · -- the sine non-positive on the range: the cosine rises
    have hs0 : ∀ z, toReal l ≤ z → z ≤ toReal u → 0 ≤ -Real.sin z := fun z hz1 hz2 => by
      have := toReal_le_of_le hc
      rw [toReal_zero] at this
      linarith [lip_upper Real.abs_sin_sub_sin_le (le_sinUp n _) hz1 hz2]
    have hd : ∀ z, HasDerivAt Real.cos (-Real.sin z) z := Real.hasDerivAt_cos
    have hm := monotoneOn_of_nonneg Real.continuous_cos hd hs0
    exact ⟨le_trans (cosDown_le n l) (hm hlu hx h1), le_trans (hm hx huu h2) (le_cosUp n u)⟩
  · exact midpoint_form Real.abs_cos_sub_cos_le
      (fun z => ⟨Real.neg_one_le_cos z, Real.cos_le_one z⟩) (cosDown_le n _) (le_cosUp n _) h1 h2

theorem sinRange_mem (n : ℕ) {l u : 𝕋} {x : ℝ} (h1 : toReal l ≤ x)
    (h2 : x ≤ toReal u) : -- --- CONCL ---
    toReal (sinRange n l u).inf ≤ Real.sin x ∧
      Real.sin x ≤ toReal (sinRange n l u).sup := by -- --- PROOF ---
  have hl : toReal l ≤ toReal u := le_trans h1 h2
  have hlu : toReal l ∈ Set.Icc (toReal l) (toReal u) := ⟨le_rfl, hl⟩
  have huu : toReal u ∈ Set.Icc (toReal l) (toReal u) := ⟨hl, le_rfl⟩
  have hx : x ∈ Set.Icc (toReal l) (toReal u) := ⟨h1, h2⟩
  simp only [sinRange]
  split_ifs with hs hc
  · -- the cosine non-negative on the range: the sine rises
    have hc0 : ∀ z, toReal l ≤ z → z ≤ toReal u → 0 ≤ Real.cos z := fun z hz1 hz2 => by
      have := toReal_le_of_le hs
      rw [toReal_zero] at this
      exact le_trans this (lip_lower Real.abs_cos_sub_cos_le (cosDown_le n _) hz1 hz2)
    have hm := monotoneOn_of_nonneg Real.continuous_sin Real.hasDerivAt_sin hc0
    exact ⟨le_trans (sinDown_le n l) (hm hlu hx h1), le_trans (hm hx huu h2) (le_sinUp n u)⟩
  · -- the cosine non-positive on the range: the sine falls
    have hc0 : ∀ z, toReal l ≤ z → z ≤ toReal u → 0 ≤ -Real.cos z := fun z hz1 hz2 => by
      have := toReal_le_of_le hc
      rw [toReal_zero] at this
      linarith [lip_upper Real.abs_cos_sub_cos_le (le_cosUp n _) hz1 hz2]
    have hd : ∀ z, HasDerivAt Real.sin (-(-Real.cos z)) z := fun z => by
      rw [neg_neg]; exact Real.hasDerivAt_sin z
    have ha := antitoneOn_of_nonneg Real.continuous_sin hd hc0
    exact ⟨le_trans (sinDown_le n u) (ha hx huu h2), le_trans (ha hlu hx h1) (le_sinUp n l)⟩
  · exact midpoint_form Real.abs_sin_sub_sin_le
      (fun z => ⟨Real.neg_one_le_sin z, Real.sin_le_one z⟩) (sinDown_le n _) (le_sinUp n _) h1 h2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
