module

public import CORALean.NN.Layers.Definitions.Relu
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Which end ReLU's gap above a line is taken at

Over a crossing box `l < 0 < u`, ReLU rises above the line `λ t` by `(1 - λ) u` at the right
end and by `-λ l` at the left, and the larger is the gap: the right one for `λ ≤ u / (u - l)`,
the left one beyond. These are the upper lines of the two families of [1, Fig. 1], `λ x̂ +
u (1 - λ)` and `λ (x̂ - l)`, and the gap times `u - l` their areas [1, Eq. 3], [1, Eq. 4]: the
first falls in `λ`, the second rises, and both equal `-u l / (u - l)` at the secant slope.
`relu_bounds_of_slope` is that each family is sound.

## Inputs
* `lam` – slope of the line
* `l` – lower end of the box
* `u` – upper end of the box

## Hypotheses
* `hl` – box starts below zero
* `hu` – box ends above zero

## Conclusion
* the gap is taken at the upper end for small slopes and at the lower end otherwise

## References

* [1] G. Singh, T. Gehr, M. Mirman, M. Püschel and M. Vechev. "Fast and Effective Robustness
      Certification". NeurIPS 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem reluGapOfSlope_eq_ite {lam l u : ℝ} (hl : l < 0) (hu : 0 < u) : -- --- CONCL ---
    reluGapOfSlope lam l u
      = if lam ≤ u / (u - l) then (1 - lam) * u else -(lam * l) := by -- --- PROOF ---
  have hw : 0 < u - l := by linarith
  -- `(1 - λ) u ≥ -λ l` is `λ (u - l) ≤ u`
  have key : -(lam * l) ≤ (1 - lam) * u ↔ lam ≤ u / (u - l) := by
    rw [le_div_iff₀ hw]; constructor <;> intro h <;> linarith
  unfold reluGapOfSlope
  split_ifs with h
  · exact max_eq_left (key.mpr h)
  · exact max_eq_right (le_of_lt (not_le.mp (fun h' => h (key.mp h'))))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
