import CORALean.ContSet.PolyZonotope.Real.Operations.ContainsExactCora1D
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin

/-!
# CORA's exact `contains` for a 1-D polynomial zonotope uses its zonotope enclosure

`pZ = polyZonotope(0, [1 1], [], [1 2])` is `{α + α² : |α| ≤ 1} = [-1/4, 2]`, while
`zonotope(pZ)` is `0.5 + [-1,1] + [-0.5,0.5] = [-1, 2]`. `contains(pZ, -0.5, 'exact')`
returns `true`, yet `-0.5 ∉ pZ`, since `α² + α + 1/2 = (α + 1/2)² + 1/4 > 0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.containsExactCora1D_counterexample :
    PolyZonotope.containsExactCora1D
        (⟨1, 2, 0, 0, ![![1], ![1]], ![![1, 2]], Fin.elim0⟩ : PolyZonotope (Vec ℝ 1)) ![-1 / 2] ∧
      (![-1 / 2] : Vec ℝ 1) ∉
        (⟨1, 2, 0, 0, ![![1], ![1]], ![![1, 2]], Fin.elim0⟩ :
          PolyZonotope (Vec ℝ 1)).construct := by -- --- PROOF ---
  constructor
  · -- the enclosure is `1/2 + β₀ + β₁/2`: take `β = (-1, 0)`
    refine ⟨![-1, 0], ?_, ?_⟩
    · intro j
      fin_cases j
      · show |(-1 : ℝ)| ≤ 1
        norm_num
      · show |(0 : ℝ)| ≤ 1
        norm_num
    · simp [PolyZonotope.zonotopeCora, PolyZonotope.coraWeight, Fin.sum_univ_succ,
        Fin.append, Fin.addCases]
      erw [Fin.sum_univ_two]
      simp
      funext i
      fin_cases i
      norm_num
  · rintro ⟨a, β, ha, -, hx⟩
    have h := congrFun hx 0
    simp [PolyZonotope.monomial, Fin.sum_univ_two] at h
    nlinarith [sq_nonneg (a 0 + 1 / 2)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
