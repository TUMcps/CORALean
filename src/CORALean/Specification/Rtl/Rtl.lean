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

* [1] [H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". Automated Technology for Verification and Analysis,
      2016.](../../../../references/2016/roehm-atva-stl-model-checking.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   26-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A reachset temporal logic formula over leaves `L`: a leaf, conjunction, disjunction, or a next
with a time shift. -/
inductive Rtl (τ L : Type)
  | all (lhs : L)
  | and (lhs rhs : Rtl τ L)
  | or (lhs rhs : Rtl τ L)
  | next (time : τ) (lhs : Rtl τ L)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
