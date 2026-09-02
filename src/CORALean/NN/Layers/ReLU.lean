import CORALean.NN.Layers.Activation

/-!
# The ReLU layer

CORA's `nnReLULayer`. The one standard activation whose relaxation carries a
slope, and it does so because the argument is elementary: `max t 0` is convex,
so it lies above every line through the origin with slope in `[0,1]` and below
that line raised by the most it departs from it over the neuron's range.

Both of those bounds are checked at the ends of the range, so the whole
relaxation is `0 ≤ relu t - λ t ≤ max ((1-λ) u) (-λ l)` — one statement covering
a neuron that is always active, one that is always inactive, and one that
crosses.

`reluSlope` is where the precision is chosen and not where the soundness is: any
slope in `[0,1]` is sound, and the secant `u / (u - l)` is picked because it
makes the two ends of the gap equal, so nothing is spent on either side. On a
stable neuron the slope is `1` or `0` and the gap is zero — the layer is then
exact, which is what makes the enclosure worth computing bounds for.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

def relu (t : ℝ) : ℝ := max t 0

/-- Exact on a stable neuron, the secant on a crossing one. -/
noncomputable def reluSlope (l u : ℝ) : ℝ :=
  if u ≤ 0 then 0 else if 0 ≤ l then 1 else u / (u - l)

/-- How far `relu` rises above the line of slope `lam` through the origin, over
`[l, u]`. A function of the slope and not of `reluSlope`, since that is what a
layer choosing its slope some other way — a float one, which has no division to
compute the secant with — measures its own error against. -/
def reluGapOfSlope (lam l u : ℝ) : ℝ := max ((1 - lam) * u) (-(lam * l))

noncomputable def reluGap (l u : ℝ) : ℝ := reluGapOfSlope (reluSlope l u) l u

theorem reluSlope_nonneg (l u : ℝ) : 0 ≤ reluSlope l u := by
  rw [reluSlope]
  split
  · exact le_rfl
  · rename_i hu
    split
    · exact zero_le_one
    · rename_i hl
      replace hu : 0 < u := not_le.mp hu
      replace hl : l < 0 := not_le.mp hl
      exact div_nonneg (le_of_lt hu) (by linarith)

theorem reluSlope_le_one (l u : ℝ) : reluSlope l u ≤ 1 := by
  rw [reluSlope]
  split
  · exact zero_le_one
  · rename_i hu
    split
    · exact le_rfl
    · rename_i hl
      replace hu : 0 < u := not_le.mp hu
      replace hl : l < 0 := not_le.mp hl
      rw [div_le_one (by linarith)]
      linarith

/-- Above the line, and below it raised by the gap — the two ends of the
relaxation, before it is recentred. Stated for an arbitrary slope in `[0,1]`,
which is all convexity gives and all either layer needs: the choice of slope
never enters. -/
theorem relu_bounds_of_slope {lam l u t : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (hl : l ≤ t) (hu : t ≤ u) :
    0 ≤ relu t - lam * t ∧ relu t - lam * t ≤ reluGapOfSlope lam l u := by
  rcases le_total 0 t with ht | ht
  · have hrt : relu t = t := max_eq_left ht
    refine ⟨by rw [hrt]; nlinarith, ?_⟩
    rw [hrt, reluGapOfSlope]
    exact le_trans (by nlinarith) (le_max_left _ _)
  · have hrt : relu t = 0 := max_eq_right ht
    refine ⟨by rw [hrt]; nlinarith, ?_⟩
    rw [hrt, reluGapOfSlope]
    exact le_trans (by nlinarith) (le_max_right _ _)

theorem aux_relu_bounds {l u t : ℝ} (hl : l ≤ t) (hu : t ≤ u) :
    0 ≤ relu t - reluSlope l u * t ∧ relu t - reluSlope l u * t ≤ reluGap l u :=
  relu_bounds_of_slope (reluSlope_nonneg l u) (reluSlope_le_one l u) hl hu

/-- Recentred, so that the error is half the gap in each direction. -/
noncomputable def reluRelaxation : Relaxation relu where
  slope := reluSlope
  offset l u := reluGap l u / 2
  error l u := reluGap l u / 2
  sound hl hu := by
    obtain ⟨hlow, hhigh⟩ := aux_relu_bounds hl hu
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩

namespace Layer

open Matrix ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat ℝ) S] [IntervalOuter S] [OfInterval S] {n : ℕ}

noncomputable def relu : Layer S n n := Layer.activation reluRelaxation

end Layer

end CORALean.Real
