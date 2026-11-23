module

public import CORALean.NN.Layers.Operations.ExpChordRelaxation
public import CORALean.NN.Layers.Theorems.OfBandEnclosesWhere
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

/-!
# The chord relaxation of the exponential is sound

At the stored slope `m`, `g(x) = e^x - m x` is convex, so on `[l, u]` it is at most the larger
of `g(l)` and `g(u)`, each rounded up. For `m > 0`, `e^x ≥ m (1 + x - log m)` (`add_one_le_exp`
at `x - log m`) puts `g` above `m - m log m`; for `m ≤ 0`, `g` grows and `g(l)` is the least;
`-m u` is below `g` for `m ≥ 0` as `e^x > 0`. The margin is not negative, so
`Relaxation.ofBand_enclosesWhere` concludes. `expUp` bounds `e^u` only for `u ≤ 2ᵏ/2`, as for
`expRelaxation`, so the relaxation is sound on those boxes.

## Inputs
* `k` – the exponential's reduction depth
* `p` – the logarithm's bisection steps
* `τ` – the least width the chord divides by
* `w` – the margin's factor

## Hypotheses
* `hw` – the factor is not negative

## Conclusion
* the relaxation is sound for the exponential on the boxes with `u ≤ 2ᵏ/2`
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

/-- The real band: `e^t - m t` on `[l, u]` is at most the larger of its values at the ends. -/
private theorem aux_exp_sub_le_max (m : ℝ) {l u t : ℝ} (hl : l ≤ t) (hu : t ≤ u) : -- --- CONCL ---
    Real.exp t - m * t ≤ max (Real.exp l - m * l) (Real.exp u - m * u) := by -- --- PROOF ---
  have hconv : ConvexOn ℝ Set.univ (fun x => Real.exp x - m * x) :=
    convexOn_exp.sub (concaveOn_const (c := (0 : ℝ)) convex_univ |>.add
      ((LinearMap.mul ℝ ℝ m).concaveOn convex_univ) |>.congr ?_)
  · exact hconv.le_max_of_mem_Icc (Set.mem_univ l) (Set.mem_univ u) ⟨hl, hu⟩
  · intro x _; simp

/-- For `m > 0`, `e^t - m t` is at least `m - m log m`, its minimum over the line. -/
private theorem aux_closed_le {m : ℝ} (hm : 0 < m) (t : ℝ) :
    m - m * Real.log m ≤ Real.exp t - m * t := by
  have h := Real.add_one_le_exp (t - Real.log m)
  rw [Real.exp_sub, Real.exp_log hm, le_div_iff₀ hm] at h
  nlinarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem expChordRelaxation_enclosesWhere (k p : ℕ) (τ : 𝕋) {w : 𝕋}
    (hw : 0 ≤ toReal w) : -- --- CONCL ---
    (expChordRelaxation k p τ w).EnclosesWhere Real.exp
      fun _ u => toReal u ≤ 2 ^ k / 2 := by -- --- PROOF ---
  refine Relaxation.ofBand_enclosesWhere (fun {l u t} hP hl hu => ?_) (fun {l u} hP => ?_)
  · -- the slope is not negative
    set m := step_expChordSlope k τ l u with hmdef
    have hm0 : 0 ≤ toReal m := by
      rw [hmdef, step_expChordSlope, toReal_maximum, toReal_zero]; exact le_max_right _ _
    have hlb : toReal l ≤ 2 ^ k / 2 := le_trans (le_trans hl hu) hP
    constructor
    · -- the lower end: the closed-form minimum, `g(l)`, or `-m u`
      show toReal (step_expChordLo k p τ l u) ≤ _
      unfold step_expChordLo
      rw [← hmdef]
      dsimp only
      split_ifs with h1 h2
      · -- `m > 0`: `m (1 + t - log m) ≤ e^t`, the logarithm rounded up
        have hm := toReal_lt_of_ltStrict h1
        rw [toReal_zero] at hm
        have hlog := le_logUp k p m hm
        have h3 := mul_le_mulUp m (logUp k p m)
        have h4 := subDown_le_sub m (mulUp m (logUp k p m))
        have h5 := mul_le_mul_of_nonneg_left hlog hm.le
        linarith [aux_closed_le hm t]
      · -- `m ≤ 0`: `g` grows, `g(l)` is the least
        have hm := toReal_le_of_le h2
        rw [toReal_zero] at hm
        have h3 := subDown_le_sub (expDown k l) (mulUp m l)
        have h4 := mul_le_mulUp m l
        have h5 := expDown_le k l
        have h6 := Real.exp_le_exp.2 hl
        nlinarith
      · have h3 := mul_le_mulUp m u
        rw [toReal_neg]
        nlinarith [Real.exp_pos t]
    · -- the upper end: the larger of the ends, by convexity
      show _ ≤ toReal (step_expChordHi k τ l u)
      unfold step_expChordHi
      rw [← hmdef]
      dsimp only
      rw [toReal_maximum]
      have hL := le_expUp k l hlb
      have hU := le_expUp k u hP
      have h1 := sub_le_subUp (expUp k l) (mulDown m l)
      have h2 := sub_le_subUp (expUp k u) (mulDown m u)
      have h3 := mulDown_le_mul m l
      have h4 := mulDown_le_mul m u
      have hmax := aux_exp_sub_le_max (toReal m) hl hu
      rcases le_total (Real.exp (toReal l) - toReal m * toReal l)
        (Real.exp (toReal u) - toReal m * toReal u) with h | h
      · rw [max_eq_right h] at hmax
        exact le_trans hmax (le_trans (by linarith) (le_max_right _ _))
      · rw [max_eq_left h] at hmax
        exact le_trans hmax (le_trans (by linarith) (le_max_left _ _))
  · -- the margin: `e^u` and `m max(|l|, |u|)` are not negative
    unfold step_expChordMargin
    dsimp only
    set m := step_expChordSlope k τ l u with hmdef
    have hm0 : 0 ≤ toReal m := by
      rw [hmdef, step_expChordSlope, toReal_maximum, toReal_zero]; exact le_max_right _ _
    have hU := le_expUp k u hP
    have hk : 0 ≤ toReal (maximum (absolute l) (absolute u)) := by
      rw [toReal_maximum, toReal_absolute]; exact le_trans (abs_nonneg _) (le_max_left _ _)
    have h1 := mul_le_mulUp m (maximum (absolute l) (absolute u))
    have h2 := add_le_addUp (expUp k u) (mulUp m (maximum (absolute l) (absolute u)))
    have h3 := mul_le_mulUp (addUp (expUp k u) (mulUp m (maximum (absolute l) (absolute u)))) w
    have hpos : 0 ≤ toReal (addUp (expUp k u) (mulUp m (maximum (absolute l) (absolute u)))) := by
      nlinarith [Real.exp_pos (toReal u)]
    nlinarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
