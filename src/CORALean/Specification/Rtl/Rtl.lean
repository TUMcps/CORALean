module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Reachset temporal logic formulas

CORA's `rtl` (`specification/@rtl/rtl.m`): an RTL formula, a tree with the node types `'all'` (`Aϱ`,
the leaf, holding an `stl` formula `lhs`), `'&'`, `'|'` and `'next'` (`Xₐψ`, with the time shift
`time`). `Rtl L` is that tree over any type `L` of leaves (in CORA, `stl` objects). The class has
no `until` and `release` nodes of [1, Def. 1]: `stl2rtl` produces only the four.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

inductive Rtl (L : Type)
  | all (lhs : L)
  | and (lhs rhs : Rtl L)
  | or (lhs rhs : Rtl L)
  | next (time : ℝ) (lhs : Rtl L)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
