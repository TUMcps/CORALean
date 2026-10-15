module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The center need not lie in the set

With a zero exponent column the factor `0` does not reach the center: for
`c = 0`, `G = [2 1]`, `E = [0 1]` the set is `{2 + α : |α| ≤ 1} = [1, 3]`, which misses `c`.
CORA's `@polyZonotope/contains_` with `'approx'` nevertheless returns `true` for the point `c`
(`withinTol(S(:,i), pZ.c)`), and `removeRedundantExponents` keeps the zero column; the float
`containsPointApprox` takes the shortcut only where no column is zero.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.center_not_mem_counterexample :
    (⟨1, 2, 0, 0, ![![2], ![1]], ![![0, 1]], Fin.elim0⟩ : PolyZonotope (Vec ℝ 1)).c ∉
      (⟨1, 2, 0, 0, ![![2], ![1]], ![![0, 1]], Fin.elim0⟩ :
        PolyZonotope (Vec ℝ 1)).construct := by -- --- PROOF ---
  rintro ⟨a, β, ha, -, hx⟩
  -- the first coordinate reads `0 = 2 + α`
  have h := congrFun hx 0
  simp [PolyZonotope.monomial, Fin.sum_univ_two] at h
  have := (abs_le.mp (ha 0)).1
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
