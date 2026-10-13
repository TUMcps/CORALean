module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-!
# The single-machine-infinite-bus field

[1, Sec. 4.4]: neglecting the mechanical-power dynamics of the generator model [1, Eq. 1] (so
`P_m` is a constant) and inserting `Θ = 0` and `Ψ_g = -π/2` into the active power of
[1, Eq. 2], `P_g = E V |Y_g| cos(Ψ_g + δ - Θ) - V² |Y_g| cos Ψ_g`, gives the printed field
`ẋ₁ = x₂`, `ẋ₂ = (P_m - E V |Y_g| sin x₁ - D x₂)/M` in `x₁ = δ`, `x₂ = ω - ω_s`, the
frequency deviation, where [1, Eq. 6] numbers the state as `ω` itself; only so does `ẋ₁ = x₂`
hold. Both lines of Eq. 1 are checked: `δ̇ = ω - ω_s` and
`ω̇ = -(D/M)(ω - ω_s) + P_m/M - P_g/M`. `Y` stands for `|Y_g|`.

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

theorem infiniteBus_field (M D P_m E V Y δ ω ω_s : ℝ) :
    let Θ : ℝ := 0                                                   -- the infinite bus
    let Ψ : ℝ := -(Real.pi / 2)                                      -- `Ψ_g = -π/2`
    let P_g := E * V * Y * Real.cos (Ψ + δ - Θ) - V ^ 2 * Y * Real.cos Ψ   -- Eq. 2
    let x₁ := δ
    let x₂ := ω - ω_s
    ω - ω_s = x₂ ∧                                                    -- Eq. 1, `δ̇`
      -(D / M) * (ω - ω_s) + P_m / M - P_g / M =                     -- Eq. 1, `ω̇`
        (P_m - E * V * Y * Real.sin x₁ - D * x₂) / M := by -- --- PROOF ---
  intro Θ Ψ P_g x₁ x₂
  refine ⟨rfl, ?_⟩
  have hc : Real.cos (Ψ + δ - Θ) = Real.sin δ := by
    simp only [Ψ, Θ, sub_zero]
    rw [show -(Real.pi / 2) + δ = δ - Real.pi / 2 by ring, Real.cos_sub_pi_div_two]
  have hΨ : Real.cos Ψ = 0 := by simp [Ψ]
  simp only [P_g, hc, hΨ, x₁, x₂]
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
