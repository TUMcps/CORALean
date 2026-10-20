module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.InvFactorialBoundsFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.FactorialDownFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.FactorialUpFloat

@[expose] public section

/-!
# `MatExp.invFactorialBounds` encloses `1 / k!`

The low bound divides `one` by an upper bound of `k!` and compares reciprocals
(`one_div_le_one_div_of_le`); the high bound is exactly `one_div_le_divUp` at
`factorialDown`'s two facts.

## Inputs
* `k` – factorial argument

## Hypotheses
* none

## Conclusion
* the float interval encloses the inverse factorial
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.invFactorialBounds_mem (k : ℕ) : -- --- CONCL ---
    toReal (MatExp.invFactorialBounds (𝕋 := 𝕋) k).inf ≤ (Nat.factorial k : ℝ)⁻¹
      ∧ (Nat.factorial k : ℝ)⁻¹
        ≤ toReal (MatExp.invFactorialBounds (𝕋 := 𝕋) k).sup := by -- --- PROOF ---
  have hfpos : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hb := MatExp.factorial_le_factorialUp (𝕋 := 𝕋) k
  have hf := MatExp.factorialDown_mem (𝕋 := 𝕋) k
  refine ⟨?_, ?_⟩
  · rw [MatExp.invFactorialBounds]
    have hpos : (0 : ℝ) < toReal (MatExp.factorialUp (𝕋 := 𝕋) k) := lt_of_lt_of_le hfpos hb
    have hd := divDown_le_div (one : 𝕋) (MatExp.factorialUp (𝕋 := 𝕋) k) hpos
    rw [toReal_one] at hd
    calc toReal (divDown one (MatExp.factorialUp (𝕋 := 𝕋) k))
        ≤ 1 / toReal (MatExp.factorialUp (𝕋 := 𝕋) k) := hd
      _ ≤ 1 / (Nat.factorial k : ℝ) := one_div_le_one_div_of_le hfpos hb
      _ = (Nat.factorial k : ℝ)⁻¹ := one_div _
  · rw [MatExp.invFactorialBounds, inv_eq_one_div]
    exact one_div_le_divUp hf.1 hf.2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
