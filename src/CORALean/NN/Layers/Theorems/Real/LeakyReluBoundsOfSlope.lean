import CORALean.NN.Layers.Definitions.LeakyRelu
import Mathlib.Tactic.Linarith

/-!
# Leaky ReLU between a line and the line raised

For a slope `m` in `[α, 1]` through the origin, `leakyRelu α t - m t` is non-negative and, on
`[l, u]`, at most the larger of its values at the two ends: it is `max (p t) (q t)` with
`p ≤ 0 ≤ q`, so the first piece is largest at `l` and the second at `u`.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem leakyRelu_bounds_of_slope {α m l u t : ℝ} (h0 : α ≤ m) (h1 : m ≤ 1)
    (hl : l ≤ t) (hu : t ≤ u) :
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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
