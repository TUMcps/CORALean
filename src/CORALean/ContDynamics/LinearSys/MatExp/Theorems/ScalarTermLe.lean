import CORALean.ContDynamics.LinearSys.MatExp.Enclosures
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.FactorialMulPowLe

/-!
# The scalar core of the exponential's tail estimate

`(η+1+i)!` outgrows `(η+1)!` by at least `(η+2)` a step, which turns the tail
past order `η` into a geometric series of ratio `c / (η+2)`. Stated on its own,
at a bare scalar `c`, because the correction matrix bounds a different series
with exactly this shape and reuses it rather than re-deriving it.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The scalar core of the tail estimate: the factorial outgrows the power fast
enough that the tail is dominated by a geometric series. Stated on its own
because the correction matrix bounds a different series with the same shape. -/
theorem scalar_term_le {c : ℝ} (hc : 0 ≤ c) (η i : ℕ) :
    (Nat.factorial (i + (η + 1)) : ℝ)⁻¹ * c ^ (i + (η + 1))
      ≤ (c ^ (η + 1) / Nat.factorial (η + 1)) * (c / ((η : ℝ) + 2)) ^ i := by -- --- PROOF ---
  rw [Nat.add_comm i (η + 1)]
  have hfac : ((Nat.factorial (η + 1) : ℝ) * ((η : ℝ) + 2) ^ i)
      ≤ (Nat.factorial ((η + 1) + i) : ℝ) := by
    have hcast : ((Nat.factorial (η + 1) * ((η + 1) + 1) ^ i : ℕ) : ℝ)
        ≤ ((Nat.factorial ((η + 1) + i) : ℕ) : ℝ) :=
      Nat.cast_le.mpr (factorial_mul_pow_le (η + 1) i)
    push_cast at hcast
    convert hcast using 3
    ring
  -- the factorial bound inverts into the geometric ratio `c / (η + 2)`
  calc (Nat.factorial ((η + 1) + i) : ℝ)⁻¹ * c ^ ((η + 1) + i)
      ≤ ((Nat.factorial (η + 1) : ℝ) * ((η : ℝ) + 2) ^ i)⁻¹ * c ^ ((η + 1) + i) := by gcongr
    _ = (c ^ (η + 1) / Nat.factorial (η + 1)) * (c / ((η : ℝ) + 2)) ^ i := by
        rw [div_pow, pow_add]
        field_simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
