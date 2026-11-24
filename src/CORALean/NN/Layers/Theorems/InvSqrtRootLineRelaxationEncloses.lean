module

public import CORALean.NN.Layers.Operations.InvSqrtRootLineRelaxation
public import CORALean.NN.Layers.Theorems.OfBandEnclosesWhere
public import CORALean.Global.Float.SqrtDownCoraLe
public import CORALean.Global.Float.LogDownPosLe
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.Mul

@[expose] public section

/-!
# The line of the inverse square root is sound

At the stored slope `m`, whatever it came to, `g(x) = 1 / √x - m x` is convex on `x > 0` (`x⁻¹`
convex and falling, `√x` concave), so on `[l, u]` it is at most the larger of `g(l)` and `g(u)`,
each rounded up. For `m < 0` and `c > 0` with `c³ = -2 m`, at `w = 1 / √x`,
`w - m x - (3 / 2) c = (w - c)² (2 w + c) / (2 w²) ≥ 0`; the computed `c` is below the real one as
`log` from below, the quotient by `3` and `exp` from below are. For `0 ≤ m`, `g` falls and `g(u)`
is the least; otherwise `g > -m x`, at least its smaller end value, and `g > 0` for `m < 0`. The
margin is zero, so `Relaxation.ofBand_enclosesWhere` concludes, on the boxes with `0 < l`.

## Inputs
* `regression` – the least-squares slope, else Singh's
* `k` – the exponential's reduction depth
* `p` – the square root's Newton steps and the logarithm's bisection steps

## Hypotheses
* none

## Conclusion
* the line is sound for the inverse square root on the boxes with `0 < l`
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

/-- `1 / √t - m t` on `[l, u] ⊆ (0, ∞)` is at most the larger of its end values. -/
private theorem aux_le_max (m : ℝ) {l u t : ℝ} (h0 : 0 < l) (hl : l ≤ t)
    (hu : t ≤ u) : -- --- CONCL ---
    (Real.sqrt t)⁻¹ - m * t ≤
      max ((Real.sqrt l)⁻¹ - m * l) ((Real.sqrt u)⁻¹ - m * u) := by -- --- PROOF ---
  have himg : Real.sqrt '' Set.Ioi 0 = Set.Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact Real.sqrt_pos.2 hx
    · intro hy; exact ⟨y ^ 2, Set.mem_Ioi.2 (pow_pos hy 2), Real.sqrt_sq (le_of_lt hy)⟩
  have hinv : ConvexOn ℝ (Real.sqrt '' Set.Ioi 0) fun x : ℝ => x ^ (-1 : ℤ) := by
    rw [himg]; exact convexOn_zpow (-1)
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-1 : ℤ)) (Real.sqrt '' Set.Ioi 0) := by
    rw [himg]
    intro a ha b _ hab
    simp only [zpow_neg_one]
    exact inv_anti₀ ha hab
  have hsq : ConcaveOn ℝ (Set.Ioi 0) Real.sqrt :=
    Real.strictConcaveOn_sqrt.concaveOn.subset Set.Ioi_subset_Ici_self (convex_Ioi 0)
  have hconv : ConvexOn ℝ (Set.Ioi 0) (fun x => (Real.sqrt x)⁻¹ - m * x) :=
    ((hinv.comp_concaveOn hsq hanti).sub ((LinearMap.mul ℝ ℝ m).concaveOn (convex_Ioi 0))).congr
      (fun x _ => by simp)
  exact hconv.le_max_of_mem_Icc (Set.mem_Ioi.2 h0) (Set.mem_Ioi.2 (h0.trans_le (hl.trans hu)))
    ⟨hl, hu⟩

/-- For `c > 0` with `c³ = -2 m`, `1 / √t - m t` is at least `(3 / 2) c` at every `t > 0`. -/
private theorem aux_closed_le {m c : ℝ} (hc : 0 < c) (hc3 : c ^ 3 = -2 * m) {t : ℝ}
    (ht : 0 < t) : -- --- CONCL ---
    c + c / 2 ≤ (Real.sqrt t)⁻¹ - m * t := by -- --- PROOF ---
  set w := (Real.sqrt t)⁻¹ with hw
  have hw0 : 0 < w := inv_pos.2 (Real.sqrt_pos.2 ht)
  have htw : t * w ^ 2 = 1 := by
    rw [hw, inv_pow, Real.sq_sqrt ht.le, mul_inv_cancel₀ ht.ne']
  have key : 3 * c * w ^ 2 ≤ 2 * w ^ 3 + c ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (w - c)) (by positivity : (0:ℝ) ≤ 2 * w + c)]
  have hmt : -(m * t) * w ^ 2 = c ^ 3 / 2 := by
    have : -(m * t) * w ^ 2 = -m * (t * w ^ 2) := by ring
    rw [this, htw]; linarith
  have hw2 : 0 < w ^ 2 := by positivity
  rw [← sub_nonneg]
  have e : (w - m * t - (c + c / 2)) * w ^ 2 = (2 * w ^ 3 + c ^ 3 - 3 * c * w ^ 2) / 2 := by
    have : (w - m * t - (c + c / 2)) * w ^ 2 = w ^ 3 + (-(m * t) * w ^ 2) - 3 / 2 * c * w ^ 2 := by
      ring
    rw [this, hmt]; ring
  have : 0 ≤ (w - m * t - (c + c / 2)) * w ^ 2 := by rw [e]; linarith
  exact nonneg_of_mul_nonneg_left this hw2

/-- The bounds of `1 / √x - m x` from the enclosure, at `x > 0`. -/
private theorem aux_g_bounds (p : ℕ) (m x : 𝕋) (hx : 0 < toReal x) : -- --- CONCL ---
    toReal (subDown (sqrtDownCora p (divDown one x)) (mulUp m x)) ≤
        (Real.sqrt (toReal x))⁻¹ - toReal m * toReal x ∧
      (Real.sqrt (toReal x))⁻¹ - toReal m * toReal x ≤
        toReal (subUp (sqrtUp p (divUp one x)) (mulDown m x)) := by -- --- PROOF ---
  have hd := divDown_le_div one x hx
  have hu := div_le_divUp one x hx
  rw [toReal_one, one_div] at hd hu
  have hs1 := le_trans (sqrtDownCora_le p (divDown one x)) (Real.sqrt_le_sqrt hd)
  have hs2 := le_trans (Real.sqrt_le_sqrt hu) (le_sqrtUp p (divUp one x))
  rw [Real.sqrt_inv] at hs1 hs2
  have h1 := subDown_le_sub (sqrtDownCora p (divDown one x)) (mulUp m x)
  have h2 := mul_le_mulUp m x
  have h4 := sub_le_subUp (sqrtUp p (divUp one x)) (mulDown m x)
  have h5 := mulDown_le_mul m x
  constructor <;> linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem invSqrtRootLineRelaxation_enclosesWhere (regression : Bool) (k p : ℕ) : -- --- CONCL ---
    (invSqrtRootLineRelaxation (𝕋 := 𝕋) regression k p).EnclosesWhere
      (fun t => (Real.sqrt t)⁻¹) fun l _ => 0 < toReal l := by -- --- PROOF ---
  refine Relaxation.ofBand_enclosesWhere (fun {l u t} hP hl hu => ?_)
    (fun _ => by rw [toReal_zero])
  set m := step_invSqrtRootLineSlope regression p l u with hmdef
  have ht0 : 0 < t := lt_of_lt_of_le hP hl
  have hu0 : 0 < toReal u := lt_of_lt_of_le ht0 hu
  obtain ⟨hgl, hgl'⟩ := aux_g_bounds p m l hP
  obtain ⟨hgu, hgu'⟩ := aux_g_bounds p m u hu0
  have hinv0 : 0 ≤ (Real.sqrt t)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg t)
  constructor
  · -- the lower end: the closed-form minimum, the smaller end value, or below `-m x`
    show toReal (step_invSqrtRootLineLo regression k p l u) ≤ _
    unfold step_invSqrtRootLineLo
    rw [← hmdef]
    dsimp only [step_invSqrtRootLineEnclosure]
    split_ifs with h1 h2 h3
    · -- `m < 0`: `(3 / 2) c`, `c` from below
      have hm := toReal_lt_of_ltStrict h1
      rw [toReal_zero] at hm
      simp only [Bool.and_eq_true] at h2
      have hy := toReal_lt_of_ltStrict h2.1
      have h3p := toReal_lt_of_ltStrict h2.2
      rw [toReal_zero] at hy h3p
      set y := addDown (neg m) (neg m) with hydef
      have hyle : toReal y ≤ -2 * toReal m := by
        have := addDown_le_add (neg m) (neg m); rw [toReal_neg] at this; linarith
      -- `log(-2 m)` from below, then a third of it from below at either rounding of `3`
      set L := logDownPos k p y with hLdef
      have hL : toReal L ≤ Real.log (toReal y) := logDownPos_le k p y hy
      have hlogy : Real.log (toReal y) ≤ Real.log (-2 * toReal m) := Real.log_le_log hy hyle
      have hD := nsmulDown_le 3 (one : 𝕋)
      have hU := le_nsmulUp 3 (one : 𝕋)
      rw [toReal_one] at hD hU
      norm_num at hD hU
      have hq1 := divDown_le_div L (nsmulDown 3 one) h3p
      have hq2 := divDown_le_div L (nsmulUp 3 one) (by linarith)
      have hq : toReal (minimum (divDown L (nsmulDown 3 one)) (divDown L (nsmulUp 3 one))) ≤
          toReal L / 3 := by
        rw [toReal_minimum]
        rcases le_total 0 (toReal L) with h | h
        · refine le_trans (min_le_right _ _) (le_trans hq2 ?_)
          exact div_le_div_of_nonneg_left h (by norm_num) hU
        · refine le_trans (min_le_left _ _) (le_trans hq1 ?_)
          rw [div_le_div_iff₀ h3p (by norm_num)]
          nlinarith
      -- the real cube root `c`, and the computed one below it
      set c := Real.exp (Real.log (-2 * toReal m) / 3) with hcdef
      have hc : 0 < c := Real.exp_pos _
      have hc3 : c ^ 3 = -2 * toReal m := by
        rw [hcdef, ← Real.exp_nat_mul]
        push_cast
        rw [show (3:ℝ) * (Real.log (-2 * toReal m) / 3) = Real.log (-2 * toReal m) by ring,
          Real.exp_log (by linarith)]
      set c' := expDown k (minimum (divDown L (nsmulDown 3 one)) (divDown L (nsmulUp 3 one)))
      have hc' : toReal c' ≤ c :=
        le_trans (expDown_le k _) (Real.exp_le_exp.2 (le_trans hq (by linarith)))
      have hin := addDown_le_add c' (half c')
      rw [toReal_half] at hin
      rw [toReal_minimum]
      refine le_trans (min_le_right _ _) (le_trans hin (le_trans ?_ (aux_closed_le hc hc3 ht0)))
      linarith
    · -- `m < 0` and no positive `-m - m` or `3`: `g > 0`
      have hm := toReal_lt_of_ltStrict h1
      rw [toReal_zero] at hm
      rw [toReal_minimum, toReal_zero]
      refine le_trans (min_le_right _ _) ?_
      nlinarith
    · -- `0 ≤ m`: `g` falls, `g(u)` is the least
      have hm := toReal_le_of_le h3
      rw [toReal_zero] at hm
      have hs : (Real.sqrt (toReal u))⁻¹ ≤ (Real.sqrt t)⁻¹ :=
        inv_anti₀ (Real.sqrt_pos.2 ht0) (Real.sqrt_le_sqrt hu)
      rw [toReal_minimum]
      refine le_trans (min_le_right _ _) (le_trans hgu ?_)
      nlinarith
    · -- neither: `g ≥ -m x`, at least its smaller end value
      have hl' := mul_le_mulUp m l
      have hu' := mul_le_mulUp m u
      rw [toReal_minimum, toReal_neg, toReal_neg]
      rcases le_total 0 (toReal m) with h | h
      · refine le_trans (min_le_right _ _) ?_; nlinarith
      · refine le_trans (min_le_left _ _) ?_; nlinarith
  · -- the upper end: the larger end value, by convexity
    show _ ≤ toReal (step_invSqrtRootLineHi regression p l u)
    unfold step_invSqrtRootLineHi
    rw [← hmdef]
    dsimp only [step_invSqrtRootLineEnclosure]
    rw [toReal_maximum]
    exact le_trans (aux_le_max (toReal m) hP hl hu) (max_le_max hgl' hgu')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
