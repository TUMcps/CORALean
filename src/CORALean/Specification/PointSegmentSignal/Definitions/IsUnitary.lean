module

public import CORALean.Specification.PointSegmentSignal.Operations.At
public import CORALean.Specification.STLInterval.Operations.Basic

@[expose] public section

/-!
# Unitary signals

A Boolean signal is unitary if it is `true` exactly on one contiguous interval `I⁺_λ ⊆ ℝ≥0` and
`false` everywhere else ([1, Sec. 2.3 (unitary)]). `s.IsUnitary J` says that the signal `s` is
unitary with `I⁺_s = J`; the interval is determined by the signal (`STLInterval.set_injective`), and
may be empty, the signal then `false` throughout.

## Inputs
* `s` – Boolean signal
* `J` – interval

## Output
* the signal is true exactly on the interval

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `s` is unitary with `I⁺_s = J`. -/
def PointSegmentSignal.IsUnitary (s : PointSegmentSignal ℝ) (J : STLInterval ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → (s.at t = true ↔ t ∈ J.set)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
