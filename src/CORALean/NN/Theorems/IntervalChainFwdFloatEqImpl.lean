module

public import CORALean.NN.Operations.IntervalChainFwdFloat
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# The forward pass of a float interval chain is the pass its implementation runs

`step_fwdImpl` differs from `IntervalChain.fwd` only by `materialise`, the identity
(`Interval.materialise_eq`), so the two agree by induction on the chain; the compiler is told to
run the stored one.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the forward pass equals the stored pass
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =======================================  MAIN THEOREM  ======================================= --

@[csimp] theorem IntervalChain.fwd_eq_impl : -- --- CONCL ---
    @IntervalChain.fwd = @IntervalChain.step_fwdImpl := by -- --- PROOF ---
  funext 𝕋 _ n k c
  induction c with
  | nil => rfl
  | linear W b rest ih =>
    funext p
    simp only [IntervalChain.fwd, IntervalChain.step_fwdImpl, Interval.materialise_eq, ih]
  | act σE σ'E rest ih =>
    funext p
    simp only [IntervalChain.fwd, IntervalChain.step_fwdImpl, ih]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
