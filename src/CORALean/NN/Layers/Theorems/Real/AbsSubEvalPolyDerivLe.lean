module

public import CORALean.NN.Layers.Theorems.Real.AbsEvalPolyDerivSubCenterLe

@[expose] public section

/-!
# The derivative bound a bracket for σ' buys

ℝ-only, as the bracket is: the fit's own derivative is bracketed by construction, so a bracket
for `σ'` bounds what `ofSampling` asks about.

## Inputs
* `n` – polynomial degree
* `c` – fit coefficients
* `σ'` – derivative of the activation
* `lo` – lower end of the derivative bracket
* `hi` – upper end of the derivative bracket
* `l` – lower end of the box
* `u` – upper end of the box
* `x` – point in the box

## Hypotheses
* `hlo` – bracket's lower end is below the derivative
* `hhi` – bracket's upper end is above the derivative
* `hl` – point is above the lower end
* `hu` – point is below the upper end

## Conclusion
* the derivative differs from the fit's by at most the bracket's bound
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem abs_sub_evalPolyDeriv_le {n : ℕ} {c : Fin (n + 1) → ℝ} {σ' : ℝ → ℝ}
    {lo hi l u x : ℝ} (hlo : lo ≤ σ' x) (hhi : σ' x ≤ hi) (hl : l ≤ x)
    (hu : x ≤ u) : -- --- CONCL ---
    |σ' x - evalPolyDeriv c x|
      ≤ polyDerivDiff lo hi (polyDerivCenter c) (polyDerivRadius c l u) := by -- --- PROOF ---
  set ctr := polyDerivCenter c
  set rad := polyDerivRadius c l u
  obtain ⟨h₁, h₂⟩ := abs_le.mp (abs_evalPolyDeriv_sub_center_le c hl hu)
  -- each end of the difference is under the `max` the definition takes
  have hL : -|lo - ctr - rad| ≤ lo - ctr - rad := neg_abs_le _
  have hU : hi - ctr + rad ≤ |hi - ctr + rad| := le_abs_self _
  have hlm : |lo - ctr - rad| ≤ max |lo - ctr - rad| |hi - ctr + rad| := le_max_left _ _
  have hum : |hi - ctr + rad| ≤ max |lo - ctr - rad| |hi - ctr + rad| := le_max_right _ _
  show |σ' x - evalPolyDeriv c x| ≤ max |lo - ctr - rad| |hi - ctr + rad|
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
