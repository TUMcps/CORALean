module

public import CORALean.ContSet.SupportFunction.Real.SupportFunction

@[expose] public section

/-!
# The support function of a set

`h(ℓ) = sup {ℓ x | x ∈ S}`, the value `-∞` for the empty set and `+∞` for a functional the set is
unbounded in. It is a specification, not a computation: no algorithm sees the set, only a bound on
it under a functional (`SupportBound`).

## Inputs
* `S` – set

## Output
* the support function of `S`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def SupportFunction.ofSet (S : Set α) : SupportFunction α where
  h := supportFunc S

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
