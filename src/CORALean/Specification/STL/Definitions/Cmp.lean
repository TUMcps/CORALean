module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The comparisons of CORA's `stl` predicates

The four comparison operators `<`, `<=`, `>`, `>=` a predicate node of CORA's `stl` object carries
(`@stl/lt.m`, `le.m`, `gt.m`, `ge.m`), and the relation on `ℝ` each stands for.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The comparison operators of an STL predicate: `<`, `≤`, `>`, `≥`. -/
inductive STL.Cmp
  | lt
  | le
  | gt
  | ge

/-- The relation of a comparison on `ℝ`. -/
def STL.Cmp.Relates : STL.Cmp → ℝ → ℝ → Prop
  | .lt => (· < ·)
  | .le => (· ≤ ·)
  | .gt => (· > ·)
  | .ge => (· ≥ ·)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
