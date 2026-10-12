import CORALean.ContSet.PolyZonotope.Real.Theorems.IsPolytopeCexMemConstruct
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# `isPolytopeCex` is not convex

`(3, 1)` and `(-3, 1)` are in the set, their midpoint `(0, 1)` is not: `a c = 1` forces
`a = ±1`, and then `2a + b ≠ 0`.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- `(3, 1)` and `(-3, 1)` are in the set, `(0, 1)` between them is not: `a c = 1` forces
`a = ±1`, and then `2a + b ≠ 0`. -/
theorem PolyZonotope.isPolytopeCex_not_convex :
    ¬ Convex ℝ PolyZonotope.isPolytopeCex.construct := by -- --- PROOF ---
  intro hc
  -- both points are in the set, via the factors `(1, 1, 1)` and `(-1, -1, -1)`
  have hP : (![3, 1] : Vec ℝ 2) ∈ PolyZonotope.isPolytopeCex.construct := by
    rw [PolyZonotope.isPolytopeCex_mem_construct]
    refine ⟨![1, 1, 1], fun k => by fin_cases k <;> simp, ?_⟩
    funext i
    fin_cases i <;> norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hQ : (![-3, 1] : Vec ℝ 2) ∈ PolyZonotope.isPolytopeCex.construct := by
    rw [PolyZonotope.isPolytopeCex_mem_construct]
    refine ⟨![-1, -1, -1], fun k => by fin_cases k <;> simp, ?_⟩
    funext i
    fin_cases i <;> norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  -- convexity puts the midpoint in the set
  have hm := hc hP hQ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  rw [PolyZonotope.isPolytopeCex_mem_construct] at hm
  -- the midpoint is `(0, 1)`, which no factors reach
  obtain ⟨a, ha, hx⟩ := hm
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  simp at h0 h1
  have a0 := abs_le.mp (ha 0)
  have a1 := abs_le.mp (ha 1)
  have a2 := abs_le.mp (ha 2)
  nlinarith [a0.1, a0.2, a1.1, a1.2, a2.1, a2.2, sq_nonneg (a 0 - a 2), sq_nonneg (a 0 + a 2)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
