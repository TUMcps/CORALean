module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# `Zonotope.representsaPolytopeCora`, the set CORA's `representsa_(Z,'polytope')` returns

CORA's `@zonotope/representsa_.m` initialises its second output as `S = []` (line 43) and, in the
`'polytope'` case (l. 111-115), sets `res = true` and `S = polytope(S)` where it means
`polytope(Z)`. `polytope([])` is the polytope with the empty vertex list, the empty set, so
`[res,S] = representsa(Z,'polytope')` answers `true` with an `S` that is not `Z`. No call in
`~/CORA` requests that second output for `'polytope'`.

# CORA's `representsa_(Z,'polytope')` returns a set other than `Z`

For `Z = zonotope([0;0], eye(2))` the set CORA's `@zonotope/representsa_.m` returns as second
output for `'polytope'` (`S = polytope(S)` with `S = []`, line 113) is empty, while `Z` contains its
centre. Wrong output, not a soundness issue: no caller in `~/CORA` reads it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- `polytope(S)` for `S = []`: the empty vertex list, the empty set (`Z` is never read). -/
def Zonotope.representsaPolytopeCora (_Z : Zonotope (Vec ℝ n)) : Set (Vec ℝ n) :=
  ∅

end CORALean.Real

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.representsaPolytopeCora_ne_construct :
    let Z : Zonotope (Vec ℝ 2) := ⟨2, 0, ![![1, 0], ![0, 1]]⟩
    Z.representsaPolytopeCora ≠ Z.construct := by -- --- PROOF ---
  intro Z h
  -- the centre is a point of `Z` (all coefficients `0`)
  have hc : Z.c ∈ Z.construct := ⟨0, fun j => by simp, by simp⟩
  rw [← h] at hc
  exact hc

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
