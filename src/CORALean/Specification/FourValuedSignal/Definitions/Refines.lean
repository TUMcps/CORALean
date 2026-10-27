module

public import CORALean.Specification.FourValuedSignal.Operations.Basic

@[expose] public section

/-!
# One four-valued signal refines another

`s` refines `k` where every value of `k` other than ⊣₂ is that of `s`: `k` knows less, and what it
knows is right. This is [1, Sec. 4.3 (refinements)]'s `≺` with a `U₂`-signal on both sides, the
relation in which a later satisfaction signal stands to an earlier one, and the exact one to the
signal a node of the analyzer holds.

## Inputs
* `s` – the signal that knows more
* `k` – the signal that knows less

## Output
* the values of `k` other than inconclusive are those of `s`, at every time `t ≥ 0`

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       27-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

def FourValuedSignal.Refines (s k : FourValuedSignal ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → k.at t ≠ FourValued.ii → s.at t = k.at t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
