module

public import Mathlib.Data.Nat.Notation

@[expose] public section

/-!
# Four-valued logic

CORA's `fourValued` (`specification/fourValued.m`) is an enumeration on `uint32` with `False(0)`,
`Unknown(1)`, `Inconclusive(2)` and `True(3)`. `FourValued` has the same four members, and
`FourValued.code` is the stored integer. The operators are in `Operations/`; MATLAB's elementwise
extension to arrays (and its `dimensionMismatch` check) is not modelled.

`Inconclusive` is the value ⊣₂ of [1, Sec. 2.2 (values)], "we don't know whether we don't know":
the uncertainty of a computation that is not finished.

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The four truth values false, unknown, inconclusive and true. -/
inductive FourValued
  | ff
  | uu
  | ii
  | tt
  deriving DecidableEq

/-- The `uint32` CORA stores: `False(0)`, `Unknown(1)`, `Inconclusive(2)`, `True(3)`. -/
def FourValued.code : FourValued → ℕ
  | .ff => 0
  | .uu => 1
  | .ii => 2
  | .tt => 3

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
