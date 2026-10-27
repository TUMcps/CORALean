module

public import CORALean.Specification.FourValued.FourValued

@[expose] public section

/-!
# Four-valued negation

`not` of `fourValued.m`: swaps `True` and `False`, keeps `Unknown` and `Inconclusive`.

Both uncertain values stay as they are, as in [1, Fig. 3].

## Inputs
* none

## Output
* the four-valued negation

## References

* [1] [F. Lercher and M. Althoff. "Using Four-Valued Signal Temporal Logic for Incremental
      Verification of Hybrid Systems". Computer Aided Verification,
      2024.](../../../../../references/2024/lercher-cav-four-valued-stl.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `~op`. -/
def FourValued.not : FourValued → FourValued
  | .tt => .ff
  | .ff => .tt
  | .uu => .uu
  | .ii => .ii

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
