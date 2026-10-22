module

public import Mathlib.Data.Nat.Notation

@[expose] public section

/-!
# Three-valued logic

CORA's `kleene` (`specification/kleene.m`) is an enumeration on `uint32` with `False(0)`,
`Unknown(1)` and `True(2)`. `Kleene` has the same three members, and `Kleene.code` is the stored
integer. The operators of the class are in `Operations/`; MATLAB's elementwise extension to arrays
(and its `dimensionMismatch` check) is not modelled, a value being a single member.

`Unknown` is the value ⊣₁ of [1, Sec. 2.2 (values)]: Kleene's third value, for a statement that
could be true or false.

## References

* [1] F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". CAV, LNCS 14683, pp. 259-281, 2024.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The three truth values false, unknown and true. -/
inductive Kleene
  | ff
  | uu
  | tt
  deriving DecidableEq

/-- The `uint32` CORA stores for a member: `False(0)`, `Unknown(1)`, `True(2)`. -/
def Kleene.code : Kleene → ℕ
  | .ff => 0
  | .uu => 1
  | .tt => 2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
