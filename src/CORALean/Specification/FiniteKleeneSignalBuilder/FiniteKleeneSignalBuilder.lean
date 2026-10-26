module

public import CORALean.Specification.FiniteSignal.FiniteSignal
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Builder of a three-valued signal

CORA's `finiteKleeneSignalBuilder` (`specification/finiteKleeneSignalBuilder.m`): a three-valued
signal of Kleene logic [1, Sec. 2.2 (values)] is built from two Boolean `finiteSignal`s, the times
where the property `possiblyTrueSignal` can be true and where it `possiblyFalseSignal` can be false.
CORA's builder is a handle object that its methods mutate; here a method returns the new builder.
The signals are over a time type `T`: ℝ, or the scalar a float layer computes in.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A three-valued signal built from two Boolean signals: when the property can be true and when it
can be false. -/
structure FiniteKleeneSignalBuilder (T : Type) where
  possiblyTrueSignal : FiniteSignal T Bool
  possiblyFalseSignal : FiniteSignal T Bool

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
