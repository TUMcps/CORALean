module

public import CORALean.Specification.STLInterval.Operations.Basic
public import CORALean.Specification.STLInterval.Theorems.ZeroLeAddCoe

@[expose] public section

/-!
# `plus` with a number

`@stlInterval/plus.m`, the numeric branch: both bounds move by the summand, the flags stay. CORA
throws if the lower bound becomes negative; here that is the hypothesis `hc` (see `STLInterval`).

Refinement pending: CORA computes this in doubles, and its refinement generic over `𝕋` (bounds
over `𝕋`, rounded outward) is not yet written.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def STLInterval.plusNum (I : STLInterval) (c : ℝ)
    (hc : I ≠ .empty → 0 ≤ I.lowerBound + c) : STLInterval :=
  match I, hc with
  | .empty, _ => .empty
  | .nonempty l u lc rc _ hu hlt hz, hc =>
    let lb := l + c
    let ub := u + c
    stlInterval lb ub lc rc (STLInterval.zero_le_add_coe hu hlt hz c (hc (by simp)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
