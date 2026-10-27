module

public import CORALean.Specification.KleeneSignal.KleeneSignal
public import CORALean.Specification.FourValued.FourValued

@[expose] public section

/-!
# Four-valued signals

CORA's `fourValuedSignal` (`specification/signals/fourValuedSignal.m`): a four-valued signal stored
as a `kleeneSignal` and a Boolean `pointSegmentSignal` `isInconclusive` that overrides it.
`FourValuedSignal.at` is the value it denotes.

These are the `U₂`-signals Λ̃ of [1, Sec. 2.3 (signals)], here with finitely many pieces.

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   15-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A four-valued signal: a three-valued signal overridden by a Boolean signal of the inconclusive
times. -/
structure FourValuedSignal (T : Type) where
  signal : KleeneSignal T
  isInconclusive : PointSegmentSignal T
  deriving DecidableEq

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
