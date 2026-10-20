module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Theorems.ZeroLeAddCoe
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `plus` with an `interval`

`@stlInterval/plus.m`, the `stlInterval + interval` branch: the bounds move by the infimum and the
supremum of the (one-dimensional) summand, the flags stay. An empty summand, `sup < inf`, gives
`stlInterval()`. CORA throws if the lower bound becomes negative; here that is the hypothesis `hc`
(see `STLInterval`).

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (bounds
over `𝕋`, rounded outward) is not yet written.

## Inputs
* `I` – interval
* `J` – real interval

## Hypotheses
* `hc` – the lower bound stays nonnegative

## Output
* the interval plus the real interval
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def STLInterval.plusInterval (I : STLInterval) (J : Real.Interval (Vec ℝ 1))
    (hc : I ≠ .empty → ¬ J.sup 0 < J.inf 0 → 0 ≤ I.lowerBound + J.inf 0) : STLInterval :=
  match I, hc with
  | .empty, _ => .empty
  | .nonempty l u lc rc _ hu hlt hz, hc =>
    if hJ : J.sup 0 < J.inf 0 then .empty
    else
      let lb := l + J.inf 0
      let ub := u + J.sup 0
      stlInterval lb ub lc rc (STLInterval.zero_le_add_coe hu hlt hz (J.inf 0) (hc (by simp) hJ))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
