import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The equilibrium of the single-machine-infinite-bus system

[1, Sec. 4.4]: with `P_m = E = V = 1` the field `ẋ₁ = x₂`, `ẋ₂ = (P_m - E V |Y_g| sin x₁ - D x₂)/M`
(`infiniteBus_field`) vanishes at `x₀ = [arcsin(1/|Y_g|), 0]ᵀ`, "the equilibrium point".
`arcsin` inverts `sin` only on `[-1, 1]`, so `|Y_g| ≥ 1` is needed, which Table 1's `|Y_g| = 5`
meets; `M` and `D` are free. At Table 1's `M = 1/(15π)`, `D = 0.04`, `|Y_g| = 5` the field is
CORA's `models/Cora/infiniteBus.m`, `[x₂; 15π(1 - 5 sin x₁ - 0.04 x₂)]`, which cites [1].
`Y` stands for `|Y_g|`.

## References

* [1] M. Althoff. "Benchmarks for the Formal Verification of Power Systems". In Proc. of the
      9th International Workshop on Applied Verification of Continuous and Hybrid Systems
      (ARCH22), EPiC Series in Computing, vol. 90, pp. 26-43, 2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem infiniteBus_equilibrium (M D Y : ℝ) (hY : 1 ≤ Y) :
    let P_m : ℝ := 1
    let E : ℝ := 1
    let V : ℝ := 1
    let x₁ := Real.arcsin (1 / Y)
    let x₂ : ℝ := 0
    x₂ = 0 ∧ (P_m - E * V * Y * Real.sin x₁ - D * x₂) / M = 0 := by -- --- PROOF ---
  intro P_m E V x₁ x₂
  refine ⟨rfl, ?_⟩
  have hY0 : 0 < Y := by linarith
  have h1 : 1 / Y ≤ 1 := by rw [div_le_one hY0]; exact hY
  have h0 : -1 ≤ 1 / Y := by
    have : 0 < 1 / Y := by positivity
    linarith
  have hs : Real.sin x₁ = 1 / Y := Real.sin_arcsin h0 h1
  simp only [P_m, E, V, x₂, hs]
  field_simp
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
