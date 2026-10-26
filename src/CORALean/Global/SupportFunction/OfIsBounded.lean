module

public import CORALean.Global.SupportFunction.SupportFunction
public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# A bound for every bounded set

A linear functional on `Vec ℝ n` is continuous, so it is bounded above on a bounded set, and the
supremum of its values is a bound. This makes a support oracle over the bounded sets exist: an
algorithm that asks one for its polytopes, and proves at each call that the polytope is bounded,
states theorems that some oracle satisfies. An oracle over all polytopes does not exist, the empty
description being all of `Vec ℝ n`. Noncomputable, the supremum being so.

## Inputs
* `S` – bounded set
* `c` – direction

## Hypotheses
* `hS` – `S` is bounded

## Output
* the support bound `sup c(S)`

## References

None: an existence fact about CORALean's own `SupportBound`; no publication states it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def SupportBound.ofIsBounded {S : Set (Vec ℝ n)} (hS : Bornology.IsBounded S)
    (c : Vec ℝ n →ₗ[ℝ] ℝ) : SupportBound S c where
  val := sSup (c '' S)
  -- a continuous map sends a bounded set to a bounded one, which `ℝ` bounds above
  le x hx :=
    le_csSup ((LinearMap.toContinuousLinearMap c).lipschitz.isBounded_image hS).bddAbove
      ⟨x, hx, rfl⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
