module

public import CORALean.Specification.KleeneSignal.KleeneSignal
public import CORALean.Specification.FourValued.FourValued

@[expose] public section

/-!
# Four-valued signals

CORA's `fourValuedSignal` (`specification/signals/fourValuedSignal.m`): a four-valued signal stored
as a `kleeneSignal` and a Boolean `pointSegmentSignal` `isInconclusive` that overrides it. `IsValid`
asks both parts to be valid; `FourValuedSignal.at` is the value it denotes.

These are the `U₂`-signals Λ̃ of [1, Sec. 2.3 (signals)], here with finitely many pieces.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure FourValuedSignal (T : Type) where
  signal : KleeneSignal T
  isInconclusive : PointSegmentSignal T
  deriving DecidableEq

/-- Both parts are valid signals. -/
def FourValuedSignal.IsValid {T : Type} [LinearOrder T] [Zero T] (s : FourValuedSignal T) : Prop :=
  s.signal.IsValid ∧ s.isInconclusive.IsValid

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
