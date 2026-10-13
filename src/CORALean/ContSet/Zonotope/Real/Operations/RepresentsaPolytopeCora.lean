import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.representsaPolytopeCora`, the set CORA's `representsa_(Z,'polytope')` returns

CORA's `@zonotope/representsa_.m` initialises its second output as `S = []` (line 43) and, in the
`'polytope'` case (l. 111-115), sets `res = true` and `S = polytope(S)` where it means
`polytope(Z)`. `polytope([])` is the polytope with the empty vertex list, the empty set, so
`[res,S] = representsa(Z,'polytope')` answers `true` with an `S` that is not `Z`. No call in
`~/CORA` requests that second output for `'polytope'`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `polytope(S)` for `S = []`: the empty vertex list, the empty set (`Z` is never read). -/
def Zonotope.representsaPolytopeCora (_Z : Zonotope (Vec ℝ n)) : Set (Vec ℝ n) :=
  ∅

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
