module

public import CORALean.NN.Operations.IntervalChainSensitivityFloat
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# The sensitivity of a float interval chain is the pass its implementation runs

`step_sensitivityImpl` differs from `IntervalChain.sensitivity` only by `materialise` and
`materialiseMat`, the identity (`Interval.materialise_eq`, `Interval.materialiseMat_eq`), so the
two agree by induction on the chain; the compiler is told to run the stored one.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the sensitivity equals the stored pass
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =======================================  MAIN THEOREM  ======================================= --

@[csimp] theorem IntervalChain.sensitivity_eq_impl : -- --- CONCL ---
    @IntervalChain.sensitivity = @IntervalChain.step_sensitivityImpl := by -- --- PROOF ---
  funext 𝕋 _ n k c
  induction c with
  | nil => rfl
  | linear W b rest ih =>
    funext p
    simp only [IntervalChain.sensitivity, IntervalChain.step_sensitivityImpl,
      Interval.materialise_eq, Interval.materialiseMat_eq, ih]
  | act σE σ'E rest ih =>
    funext p
    simp only [IntervalChain.sensitivity, IntervalChain.step_sensitivityImpl,
      Interval.materialiseMat_eq, ih]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
