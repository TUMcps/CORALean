module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-!
# The generator's power, rewritten

[1, Eq. 2]: the active and reactive power a generator feeds into its bus, as printed after
Schavemaker and van der Sluis,
`P_g = E V |Y_g| cos(-Ψ_g - δ + Θ) - V² |Y_g| cos(-Ψ_g)`,
`Q_g = E V |Y_g| sin(-Ψ_g - δ + Θ) - V² |Y_g| sin(-Ψ_g)`,
equals the form the paper works with,
`P_g = E V |Y_g| cos(Ψ_g + δ - Θ) - V² |Y_g| cos(Ψ_g)`,
`Q_g = -E V |Y_g| sin(Ψ_g + δ - Θ) + V² |Y_g| sin(Ψ_g)`,
by `cos(-α) = cos α` and `sin(-α) = -sin α`, as the paper says. `Y` stands for `|Y_g|`.

## Inputs
* `E` – internal voltage
* `V` – bus voltage
* `Y` – admittance magnitude
* `Ψ` – admittance angle
* `δ` – rotor angle
* `Θ` – bus angle

## Hypotheses
* none

## Conclusion
* the printed active and reactive power equal the rewritten forms

## References

* [1] M. Althoff. "Benchmarks for the Formal Verification of Power Systems". Proceedings of 9th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH22),
      2022.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem generatorPower_rewrite (E V Y Ψ δ Θ : ℝ) : -- --- CONCL ---
    E * V * Y * Real.cos (-Ψ - δ + Θ) - V ^ 2 * Y * Real.cos (-Ψ) =
        E * V * Y * Real.cos (Ψ + δ - Θ) - V ^ 2 * Y * Real.cos Ψ ∧
      E * V * Y * Real.sin (-Ψ - δ + Θ) - V ^ 2 * Y * Real.sin (-Ψ) =
        -(E * V * Y * Real.sin (Ψ + δ - Θ)) + V ^ 2 * Y * Real.sin Ψ := by -- --- PROOF ---
  have h : -Ψ - δ + Θ = -(Ψ + δ - Θ) := by ring
  rw [h, Real.cos_neg, Real.cos_neg, Real.sin_neg, Real.sin_neg]
  constructor
  · ring
  · ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
