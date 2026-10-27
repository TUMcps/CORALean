module

public import CORALean.Specification.STLInterval.Theorems.RawSetOrdConnected

@[expose] public section

/-!
# The times of an interval are order connected

An `stlInterval` denotes a contiguous set of times: `Set.OrdConnected` (`rawSet_ordConnected` for
the nonempty ones). It is what makes a Boolean signal that is `true` exactly on one interval a
unitary signal in the sense of [1, Sec. 2.3 (unitary)].

## Inputs
* `J` – interval

## Hypotheses
* none

## Conclusion
* the times of the interval are order connected

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STLInterval.set_ordConnected (J : STLInterval 𝕋) : J.set.OrdConnected := by
  cases J with
  | empty => exact Set.ordConnected_empty
  | nonempty l u lc rc b c _ => exact STLInterval.rawSet_ordConnected _ _ lc rc

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
