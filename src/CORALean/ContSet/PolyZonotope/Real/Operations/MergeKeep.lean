import CORALean.ContSet.PolyZonotope.Real.Operations.Rep

/-!
# The columns `merge` keeps

One index per distinct exponent column, the least carrying it. This is
`compactKeep` without the second half of a compaction: a column whose merged
generator came out zero stays, and so does the all-zero column, because
`merge` is asked to join equal columns and nothing else.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The columns that survive a merge: those that are their own representative. -/
def PolyZonotope.mergeKeep {p h : ℕ} (E : Fin p → Fin h → ℕ) : Finset (Fin h) :=
  Finset.univ.filter fun j => PolyZonotope.rep E j = j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
