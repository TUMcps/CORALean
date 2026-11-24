module

public import CORALean.NN.Operations.IntervalChainBackpropFloat
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# The backpropagation of a float interval chain is the pass its implementation runs

`step_backpropImpl` differs from `IntervalChain.backprop` only by `materialise`, the identity
(`Interval.materialise_eq`), so the two agree by induction on the chain; the compiler is told to
run the stored one.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the backpropagation equals the stored pass
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =======================================  MAIN THEOREM  ======================================= --

@[csimp] theorem IntervalChain.backprop_eq_impl : -- --- CONCL ---
    @IntervalChain.backprop = @IntervalChain.step_backpropImpl := by -- --- PROOF ---
  funext 𝕋 _ n k c
  induction c with
  | nil => rfl
  | linear W b rest ih =>
    funext p g
    simp only [IntervalChain.backprop, IntervalChain.step_backpropImpl, Interval.materialise_eq,
      ih]
  | act σE σ'E rest ih =>
    funext p g
    simp only [IntervalChain.backprop, IntervalChain.step_backpropImpl, Interval.materialise_eq,
      ih]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
