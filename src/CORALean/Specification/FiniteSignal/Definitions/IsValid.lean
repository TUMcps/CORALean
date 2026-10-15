module

public import CORALean.Specification.FiniteSignal.FiniteSignal
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.List.Chain
public import Mathlib.Order.Basic

@[expose] public section

/-!
# What the constructor accepts

The checks of `finiteSignal.m`: non-empty arrays of the same length, strictly increasing non-
negative times, and no two consecutive equal values (so a signal has one representation).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The constructor `finiteSignal(time,value)` throws nothing. -/
def FiniteSignal.IsValid {T V : Type} [LinearOrder T] [Zero T] (s : FiniteSignal T V) : Prop :=
  s.time ≠ [] ∧ s.time.length = s.value.length ∧ s.time.Pairwise (· < ·) ∧
    s.value.IsChain (· ≠ ·) ∧ ∀ t ∈ s.time, 0 ≤ t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
