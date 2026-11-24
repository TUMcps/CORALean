module

public import CORALean.NN.Layers.Operations.SoftplusLineRelaxation
public import CORALean.NN.Layers.Theorems.OfBandEnclosesWhere
public import CORALean.Global.Float.LogDownPosLe
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-!
# The line of softplus is sound

At the stored slope `m`, whatever it came to, `g(x) = log(1 + e^x) - m x` is convex (its derivative
`e^x / (1 + e^x)` grows), so on `[l, u]` it is at most the larger of `g(l)` and `g(u)`, each
rounded up. For `0 < m < 1`, `log` is concave: at the weights `m`, `1 - m` and the points
`e^x / m`, `1 / (1 - m)`, whose mean is `1 + e^x`,
`log(1 + e^x) ≥ m (x - log m) - (1 - m) log(1 - m)`.
For `m ≤ 0`, `g` grows and `g(l)` is the least; for `1 ≤ m` it falls, `log(1 + e^x)` rising by at
most `x`'s rise, and `g(u)` is the least; otherwise `g ≥ -m x` as `log(1 + e^x) ≥ 0`.
`Relaxation.ofBand_enclosesWhere` concludes, on the boxes with `u ≤ 2ᵏ/2` that `expUp` needs.

## Inputs
* `regression` – the least-squares slope, else Singh's
* `k` – the exponential's reduction depth
* `p` – the logarithm's bisection steps

## Hypotheses
* none

## Conclusion
* the line is sound for softplus on the boxes with `u ≤ 2ᵏ/2`
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

/-- `log(1 + e^t) - m t` on `[l, u]` is at most the larger of its end values. -/
private theorem aux_le_max (m : ℝ) {l u t : ℝ} (hl : l ≤ t) (hu : t ≤ u) : -- --- CONCL ---
    Real.log (1 + Real.exp t) - m * t ≤
      max (Real.log (1 + Real.exp l) - m * l)
        (Real.log (1 + Real.exp u) - m * u) := by -- --- PROOF ---
  have hd : ∀ x : ℝ, HasDerivAt (fun x => Real.log (1 + Real.exp x))
      (Real.exp x / (1 + Real.exp x)) x := fun x =>
    ((Real.hasDerivAt_exp x).const_add 1).log (by positivity)
  have hderiv : deriv (fun x => Real.log (1 + Real.exp x)) =
      fun x => Real.exp x / (1 + Real.exp x) := funext fun x => (hd x).deriv
  have hsp : ConvexOn ℝ Set.univ (fun x => Real.log (1 + Real.exp x)) := by
    refine MonotoneOn.convexOn_of_deriv convex_univ
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) ?_
    rw [hderiv]
    intro a _ b _ hab
    have he := Real.exp_le_exp.2 hab
    dsimp only
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hconv : ConvexOn ℝ Set.univ (fun x => Real.log (1 + Real.exp x) - m * x) :=
    (hsp.sub ((LinearMap.mul ℝ ℝ m).concaveOn convex_univ)).congr (fun x _ => by simp)
  exact hconv.le_max_of_mem_Icc (Set.mem_univ l) (Set.mem_univ u) ⟨hl, hu⟩

/-- For `0 < m < 1`, `log(1 + e^t) - m t` is at least `-(m log m) - (1 - m) log(1 - m)`. -/
private theorem aux_closed_le {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) (t : ℝ) : -- --- CONCL ---
    -(m * Real.log m) - (1 - m) * Real.log (1 - m) ≤
      Real.log (1 + Real.exp t) - m * t := by -- --- PROOF ---
  have h1m : 0 < 1 - m := by linarith
  have hx : Real.exp t / m ∈ Set.Ioi (0:ℝ) := Set.mem_Ioi.2 (by positivity)
  have hy : 1 / (1 - m) ∈ Set.Ioi (0:ℝ) := Set.mem_Ioi.2 (by positivity)
  have hJ := strictConcaveOn_log_Ioi.concaveOn.2 hx hy hm0.le h1m.le (by ring)
  simp only [smul_eq_mul] at hJ
  have hmean : m * (Real.exp t / m) + (1 - m) * (1 / (1 - m)) = 1 + Real.exp t := by
    field_simp; ring
  rw [hmean, Real.log_div (Real.exp_pos t).ne' hm0.ne', Real.log_exp, one_div,
    Real.log_inv] at hJ
  linarith

/-- For `1 ≤ m`, `log(1 + e^t) - m t` falls: `g(u)` is at most `g(t)` for `t ≤ u`. -/
private theorem aux_falls {m : ℝ} (hm : 1 ≤ m) {t u : ℝ} (hu : t ≤ u) : -- --- CONCL ---
    Real.log (1 + Real.exp u) - m * u ≤ Real.log (1 + Real.exp t) - m * t := by -- --- PROOF ---
  have he : 1 ≤ Real.exp (u - t) := Real.one_le_exp (by linarith)
  have hprod : 1 + Real.exp u ≤ Real.exp (u - t) * (1 + Real.exp t) := by
    rw [mul_add, mul_one, ← Real.exp_add, sub_add_cancel]; linarith
  have hlog := Real.log_le_log (by positivity) hprod
  rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp] at hlog
  nlinarith

/-- The bounds of `log(1 + e^x) - m x` from the enclosure, the upper one for `x ≤ 2ᵏ/2`. -/
private theorem aux_g_bounds (k p : ℕ) (m x : 𝕋) (hx : toReal x ≤ 2 ^ k / 2) : -- --- CONCL ---
    toReal (subDown (logDownPos k p (onePlusExpDown k x)) (mulUp m x)) ≤
        Real.log (1 + Real.exp (toReal x)) - toReal m * toReal x ∧
      Real.log (1 + Real.exp (toReal x)) - toReal m * toReal x ≤
        toReal (subUp (logUp k p (addUp one (expUp k x))) (mulDown m x)) := by -- --- PROOF ---
  -- below: `log` from below of `1 + e^x` from below, which is at least one
  have hone : 1 ≤ toReal (onePlusExpDown k x) := by
    rw [onePlusExpDown, toReal_maximum, toReal_one]; exact le_max_left _ _
  have hle : toReal (onePlusExpDown k x) ≤ 1 + Real.exp (toReal x) := by
    rw [onePlusExpDown, toReal_maximum]
    refine max_le ?_ (le_trans (addDown_le_add one (expDown k x)) ?_)
    · rw [toReal_one]; linarith [Real.exp_pos (toReal x)]
    · rw [toReal_one]; linarith [expDown_le k x]
  have hlo := le_trans (logDownPos_le k p _ (by linarith))
    (Real.log_le_log (by linarith) hle)
  -- above: `log` from above of `1 + e^x` from above
  have hE := le_expUp k x hx
  have ha := add_le_addUp one (expUp k x)
  rw [toReal_one] at ha
  have hpos : 0 < 1 + Real.exp (toReal x) := by positivity
  have hhi := le_trans (Real.log_le_log hpos (by linarith))
    (le_logUp k p (addUp one (expUp k x)) (by linarith))
  -- `m x` rounded the other way, the differences outward
  have h1 := subDown_le_sub (logDownPos k p (onePlusExpDown k x)) (mulUp m x)
  have h2 := mul_le_mulUp m x
  have h4 := sub_le_subUp (logUp k p (addUp one (expUp k x))) (mulDown m x)
  have h5 := mulDown_le_mul m x
  constructor <;> linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem softplusLineRelaxation_enclosesWhere (regression : Bool) (k p : ℕ) : -- --- CONCL ---
    (softplusLineRelaxation (𝕋 := 𝕋) regression k p).EnclosesWhere
      (fun t => Real.log (1 + Real.exp t)) fun _ u => toReal u ≤ 2 ^ k / 2 := by -- --- PROOF ---
  refine Relaxation.ofBand_enclosesWhere (fun {l u t} hP hl hu => ?_)
    (fun _ => by rw [toReal_zero])
  set m := step_softplusLineSlope regression k p l u with hmdef
  have hlb : toReal l ≤ 2 ^ k / 2 := le_trans (le_trans hl hu) hP
  obtain ⟨hgl, hgl'⟩ := aux_g_bounds k p m l hlb
  obtain ⟨hgu, hgu'⟩ := aux_g_bounds k p m u hP
  have hsp0 : 0 ≤ Real.log (1 + Real.exp t) :=
    Real.log_nonneg (by linarith [Real.exp_pos t])
  constructor
  · -- the lower end: the closed-form minimum, the smaller end value, or below `-m x`
    show toReal (step_softplusLineLo regression k p l u) ≤ _
    unfold step_softplusLineLo
    rw [← hmdef]
    dsimp only [step_softplusLineEnclosure]
    split_ifs with h1 h2
    · -- `0 < m < 1`: the closed form, the logarithms from above
      simp only [Bool.and_eq_true] at h1
      have hm0 := toReal_lt_of_ltStrict h1.1
      have hm1 := toReal_lt_of_ltStrict h1.2
      rw [toReal_zero] at hm0
      rw [toReal_one] at hm1
      have hlm := le_logUp k p m hm0
      have htD := subDown_le_sub one m
      have htU := sub_le_subUp one m
      rw [toReal_one] at htD htU
      have htU0 : 0 < toReal (subUp one m) := by linarith
      set L := logUp k p (subUp one m) with hLdef
      have hL : Real.log (1 - toReal m) ≤ toReal L :=
        le_trans (Real.log_le_log (by linarith) htU) (le_logUp k p _ htU0)
      have hA := mul_le_mulUp m (logUp k p m)
      have hB1 := mul_le_mulUp (subDown one m) L
      have hB2 := mul_le_mulUp (subUp one m) L
      -- `(1 - m) L` lies between its values at the two roundings of `1 - m`
      have hB : (1 - toReal m) * Real.log (1 - toReal m) ≤
          max (toReal (mulUp (subDown one m) L)) (toReal (mulUp (subUp one m) L)) := by
        have hlogneg : (1 - toReal m) * Real.log (1 - toReal m) ≤ (1 - toReal m) * toReal L :=
          mul_le_mul_of_nonneg_left hL (by linarith)
        rcases le_total 0 (toReal L) with h | h
        · exact le_trans hlogneg (le_trans (by nlinarith) (le_max_right _ _))
        · exact le_trans hlogneg (le_trans (by nlinarith) (le_max_left _ _))
      have hS := subDown_le_sub (neg (mulUp m (logUp k p m)))
        (maximum (mulUp (subDown one m) L) (mulUp (subUp one m) L))
      rw [toReal_neg, toReal_maximum] at hS
      have hml : toReal m * Real.log (toReal m) ≤ toReal m * toReal (logUp k p m) :=
        mul_le_mul_of_nonneg_left hlm hm0.le
      have hc := aux_closed_le hm0 hm1 t
      rw [toReal_minimum]
      refine le_trans (min_le_right _ _) ?_
      linarith
    · -- `m ≤ 0` or `1 ≤ m`: the smaller end value
      simp only [Bool.or_eq_true] at h2
      rw [toReal_minimum]
      rcases h2 with h | h
      · have hm := toReal_le_of_le h
        rw [toReal_zero] at hm
        have hmono : Real.log (1 + Real.exp (toReal l)) ≤ Real.log (1 + Real.exp t) :=
          Real.log_le_log (by positivity) (by linarith [Real.exp_le_exp.2 hl])
        have := mul_le_mul_of_nonpos_left hl hm
        exact le_trans (min_le_left _ _) (le_trans hgl (by linarith))
      · have hm := toReal_le_of_le h
        rw [toReal_one] at hm
        exact le_trans (min_le_right _ _) (le_trans hgu (aux_falls hm hu))
    · -- neither: `g ≥ -m x`, at least its smaller end value
      have hl' := mul_le_mulUp m l
      have hu' := mul_le_mulUp m u
      rw [toReal_minimum, toReal_neg, toReal_neg]
      rcases le_total 0 (toReal m) with h | h
      · have := mul_le_mul_of_nonneg_left hu h
        exact le_trans (min_le_right _ _) (by linarith)
      · have := mul_le_mul_of_nonpos_left hl h
        exact le_trans (min_le_left _ _) (by linarith)
  · -- the upper end: the larger end value, by convexity
    show _ ≤ toReal (step_softplusLineHi regression k p l u)
    unfold step_softplusLineHi
    rw [← hmdef]
    dsimp only [step_softplusLineEnclosure]
    rw [toReal_maximum]
    exact le_trans (aux_le_max (toReal m) hl hu) (max_le_max hgl' hgu')

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
