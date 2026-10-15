module

public import CORALean.Specification.Kleene.Kleene
public import CORALean.Specification.PointSegmentSignal.Definitions.IsValid

@[expose] public section

/-!
# Three-valued signals

CORA's `kleeneSignal` (`specification/signals/kleeneSignal.m`): a Kleene-valued signal stored as
two Boolean `pointSegmentSignal`s, the Boolean part `signal` and `isUnknown`, where `isUnknown`
overrides `signal` (whose value is then irrelevant). `IsValid` asks both to be valid, as the
constructor of `pointSegmentSignal` makes them; `KleeneSignal.at` is the value it denotes.

These are the `U₁`-signals Λ of [1, Sec. 2.3 (signals)], here with finitely many pieces.

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

structure KleeneSignal (T : Type) where
  signal : PointSegmentSignal T
  isUnknown : PointSegmentSignal T
  deriving DecidableEq

/-- Both parts are valid signals. -/
def KleeneSignal.IsValid {T : Type} [LinearOrder T] [Zero T] (s : KleeneSignal T) : Prop :=
  s.signal.IsValid ∧ s.isUnknown.IsValid

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
