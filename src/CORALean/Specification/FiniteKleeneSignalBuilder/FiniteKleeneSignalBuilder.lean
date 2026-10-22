module

public import CORALean.Specification.FiniteSignal.FiniteSignal
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Builder of a three-valued signal

CORA's `finiteKleeneSignalBuilder` (`specification/finiteKleeneSignalBuilder.m`): a three-valued
signal of Kleene logic is built from two Boolean `finiteSignal`s, the times where the property
`possiblyTrueSignal` can be true and where it `possiblyFalseSignal` can be false. CORA's builder is
a handle object that its methods mutate; here a method returns the new builder.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A three-valued signal built from two Boolean signals: when the property can be true and when it
can be false. -/
structure FiniteKleeneSignalBuilder where
  possiblyTrueSignal : FiniteSignal ℝ Bool
  possiblyFalseSignal : FiniteSignal ℝ Bool

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
