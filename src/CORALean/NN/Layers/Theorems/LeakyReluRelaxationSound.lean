import CORALean.NN.Layers.Operations.LeakyReluRelaxation
import CORALean.NN.Layers.Theorems.Real.LeakyReluBoundsOfSlope

/-!
# The leaky ReLU relaxation is sound

At whatever slope the caller chose, for a stored `α ≤ 1`: the clamped slope lies in `[α, 1]`, so
`leakyRelu α t - m t` is between zero and its larger end value, which the stored gap bounds from
above; halving is exact, so the recentred line is within half the gap everywhere on the box.
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

theorem aux_leakyReluEndUp_ge (α m a : 𝕋) :
    max (toReal α * toReal a) (toReal a) - toReal m * toReal a ≤
      toReal (leakyReluEndUp α m a) := by -- --- PROOF ---
  have h1 := sub_le_subUp (maximum (mulUp α a) a) (mulDown m a)
  have h2 := toReal_maximum (mulUp α a) a
  have h3 := mul_le_mulUp α a
  have h4 := mulDown_le_mul m a
  rw [leakyReluEndUp]
  have : max (toReal α * toReal a) (toReal a) ≤ toReal (maximum (mulUp α a) a) := by
    rw [h2]; exact max_le_max h3 le_rfl
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem leakyReluRelaxation_sound (α : 𝕋) (hα : toReal α ≤ 1) (lam : 𝕋 → 𝕋 → 𝕋) :
    (leakyReluRelaxation α lam).Sound (Real.leakyRelu (toReal α)) := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  set m := maximum α (minimum one (lam l u)) with hm
  have hm0 : toReal α ≤ toReal m := by rw [hm, toReal_maximum]; exact le_max_left _ _
  have hm1 : toReal m ≤ 1 := by
    rw [hm, toReal_maximum, toReal_minimum, toReal_one]
    exact max_le hα (min_le_left _ _)
  obtain ⟨hlow, hhigh⟩ := Real.leakyRelu_bounds_of_slope hm0 hm1 hl hu
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
