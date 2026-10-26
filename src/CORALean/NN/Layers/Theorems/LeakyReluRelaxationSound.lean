module

public import CORALean.NN.Layers.Operations.LeakyReluRelaxation
public import CORALean.NN.Layers.Definitions.LeakyRelu
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The leaky ReLU relaxation is sound

At whatever slope the caller chose, for a stored `α ≤ 1`: the clamped slope lies in `[α, 1]`, so
`leakyRelu α t - m t` is between zero and its larger end value, which the stored gap bounds from
above; halving is exact, so the recentered line is within half the gap everywhere on the box.

## Inputs
* `α` – slope below zero
* `lam` – slope choice for each box

## Hypotheses
* `hα` – slope is at most one

## Conclusion
* the relaxation is sound for the leaky ReLU
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

namespace Real
/-- Leaky ReLU between a line and the line raised. -/
private theorem aux_leakyRelu_bounds_of_slope {α m l u t : ℝ} (h0 : α ≤ m) (h1 : m ≤ 1)
    (hl : l ≤ t) (hu : t ≤ u) : -- --- CONCL ---
    0 ≤ leakyRelu α t - m * t ∧
      leakyRelu α t - m * t ≤
        max (leakyRelu α l - m * l) (leakyRelu α u - m * u) := by -- --- PROOF ---
  unfold leakyRelu
  refine ⟨?_, ?_⟩
  · rcases le_total 0 t with h | h
    · have := le_max_right (α * t) t
      nlinarith
    · have := le_max_left (α * t) t
      nlinarith
  · have hp : α * t - m * t ≤ max (max (α * l) l - m * l) (max (α * u) u - m * u) := by
      refine le_trans ?_ (le_max_left _ _)
      have : α * l ≤ max (α * l) l := le_max_left _ _
      nlinarith
    have hq : t - m * t ≤ max (max (α * l) l - m * l) (max (α * u) u - m * u) := by
      refine le_trans ?_ (le_max_right _ _)
      have : u ≤ max (α * u) u := le_max_right _ _
      nlinarith
    rcases le_total (α * t) t with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
end Real


private theorem aux_leakyReluEndUp_ge (α m a : 𝕋) : -- --- CONCL ---
    Real.leakyRelu (toReal α) (toReal a) - toReal m * toReal a ≤
      toReal (leakyReluEndUp α m a) := by -- --- PROOF ---
  have h1 := sub_le_subUp (maximum (mulUp α a) a) (mulDown m a)
  have h2 := toReal_maximum (mulUp α a) a
  have h3 := mul_le_mulUp α a
  have h4 := mulDown_le_mul m a
  rw [leakyReluEndUp]
  have : Real.leakyRelu (toReal α) (toReal a) ≤ toReal (maximum (mulUp α a) a) := by
    rw [h2]; exact max_le_max h3 le_rfl
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem leakyReluRelaxation_isSound (α : 𝕋) (hα : toReal α ≤ 1) (lam : 𝕋 → 𝕋 → 𝕋) : -- --- CONCL ---
    (leakyReluRelaxation α lam).IsSound (Real.leakyRelu (toReal α)) := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  set m := maximum α (minimum one (lam l u)) with hm
  have hm0 : toReal α ≤ toReal m := by rw [hm, toReal_maximum]; exact le_max_left _ _
  have hm1 : toReal m ≤ 1 := by
    rw [hm, toReal_maximum, toReal_minimum, toReal_one]
    exact max_le hα (min_le_left _ _)
  obtain ⟨hlow, hhigh⟩ := Real.aux_leakyRelu_bounds_of_slope hm0 hm1 hl hu
  have hg : max (Real.leakyRelu (toReal α) (toReal l) - toReal m * toReal l)
      (Real.leakyRelu (toReal α) (toReal u) - toReal m * toReal u) ≤
      toReal (leakyReluGapUp α m l u) := by
    rw [leakyReluGapUp, toReal_maximum (leakyReluEndUp α m l) (leakyReluEndUp α m u)]
    exact max_le_max (aux_leakyReluEndUp_ge α m l) (aux_leakyReluEndUp_ge α m u)
  show |Real.leakyRelu (toReal α) t - (toReal m * t + toReal (half (leakyReluGapUp α m l u)))|
    ≤ toReal (half (leakyReluGapUp α m l u))
  rw [toReal_half, abs_le]
  constructor <;> linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
