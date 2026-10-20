module

public import CORALean.NN.Layers.Operations.ReluRelaxation
public import CORALean.NN.Layers.Theorems.Basic
public import CORALean.NN.Layers.Theorems.Real.ReluBoundsOfSlope
public import CORALean.NN.Layers.Theorems.ReluGapOfSlopeLe

@[expose] public section

/-!
# The ReLU relaxation is sound

At whatever slope the caller chose: clamped into `[0, 1]`, ReLU lies between the line and the
line raised by the exact gap, the stored gap bounds the exact one, and halving is exact, so the
recentered line is within half the stored gap of ReLU everywhere on the box.

## Inputs
* `lam` – slope choice for each box

## Hypotheses
* none

## Conclusion
* the relaxation is sound for ReLU
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

-- not `Matrix`: its `zero` would make `FloatOps.zero` ambiguous
open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem reluRelaxation_sound (lam : 𝕋 → 𝕋 → 𝕋) : -- --- CONCL ---
    (reluRelaxation lam).Sound Real.relu := by -- --- PROOF ---
  refine ⟨fun {l u _t} hl hu => ?_⟩
  obtain ⟨hlow, hhigh⟩ := Real.relu_bounds_of_slope (clampUnit_nonneg (lam l u))
    (clampUnit_le_one (lam l u)) hl hu
  have hg := reluGapOfSlope_le (clampUnit (lam l u)) l u
  show |Real.relu _t - (toReal (clampUnit (lam l u)) * _t
    + toReal (half (reluGapUp (clampUnit (lam l u)) l u)))|
      ≤ toReal (half (reluGapUp (clampUnit (lam l u)) l u))
  rw [toReal_half, abs_le]
  exact ⟨by linarith, by linarith⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
