module

public import CORALean.NN.Layers.Definitions.InvSqrtRelaxation
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The inverse square root's derivative bracket is nonempty

`y ↦ -(2 y √y)⁻¹` rises toward `0`, since `y √y` itself rises: the bracket `[lo l, hi u]` is
nonempty exactly because `l ≤ u`.

## Inputs
* `l` – lower end of the box
* `u` – upper end of the box

## Hypotheses
* `hl` – lower end is positive
* `hlu` – box is ordered

## Conclusion
* the lower end of the derivative bracket is at most the upper end
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem invSqrtDeriv_mono {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) :
    invSqrtDerivLo l ≤ invSqrtDerivHi u := by -- --- PROOF ---
  unfold invSqrtDerivLo invSqrtDerivHi
  have hupos : (0 : ℝ) < u := hl.trans_le hlu
  have hprod : l * Real.sqrt l ≤ u * Real.sqrt u :=
    mul_le_mul hlu (Real.sqrt_le_sqrt hlu) (Real.sqrt_nonneg l) hupos.le
  have hlpos : (0 : ℝ) < l * Real.sqrt l := by positivity
  gcongr

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
