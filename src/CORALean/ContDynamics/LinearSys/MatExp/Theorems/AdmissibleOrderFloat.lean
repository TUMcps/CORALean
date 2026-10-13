module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdmissibleOrderFloat
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# An order `admissibleOrder` returns is admissible

`List.find?` returns only an entry its test accepted, and `le`'s `true` is sound:
`nrm ≤ half (η + 2)↓ ≤ (η + 2)/2`, `nsmulDown_le` bounding the rounded count and
`half` being exact. The entry is `η₀ + k` by construction, so at least `η₀`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.admissibleOrder_spec {nrm : 𝕋} {η₀ fuel η : ℕ}
    (h : MatExp.admissibleOrder nrm η₀ fuel = some η) :
    toReal nrm / ((η : ℝ) + 2) ≤ 1 / 2 ∧ η₀ ≤ η := by -- --- PROOF ---
  rw [MatExp.admissibleOrder] at h
  have hle := toReal_le_of_le (List.find?_some (p := fun η =>
    le nrm (half (nsmulDown (η + 2) (one : 𝕋)))) h)
  obtain ⟨k, -, hk⟩ := List.mem_map.mp (List.mem_of_find?_eq_some h)
  refine ⟨?_, hk ▸ Nat.le_add_right η₀ k⟩
  -- `half` is exact and the count is rounded down, so `nrm ≤ (η + 2)/2`
  have hcount := nsmulDown_le (η + 2) (one : 𝕋)
  rw [toReal_one, mul_one] at hcount
  rw [toReal_half] at hle
  have hpos : (0 : ℝ) < (η : ℝ) + 2 := by positivity
  rw [div_le_iff₀ hpos]
  push_cast at hcount
  linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
