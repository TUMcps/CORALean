module

public import CORALean.ContSet.HPolytope.Real.Operations.NormalizeConstraints
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `normalizeConstraints` denotes the same set, exactly

Each row is divided by a positive number, or an equality row by a nonzero one, on both sides.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.normalizeConstraints_exact (P : HPolytope α) :
    P.normalizeConstraints.construct = P.construct := by -- --- PROOF ---
  ext x
  -- an inequality row, scaled by `|b|⁻¹ > 0`, and an equality row by `be⁻¹`
  have hle : ∀ i, (P.normalizeConstraints.A i) x ≤ P.normalizeConstraints.b i
      ↔ (P.A i) x ≤ P.b i := by
    intro i
    -- a zero right-hand side is untouched; else the sign of `b` picks the case
    by_cases hb : P.b i = 0
    · simp [HPolytope.normalizeConstraints, hb]
    · by_cases hp : 0 < P.b i
      · simp only [HPolytope.normalizeConstraints, hb, hp, if_false, if_true,
          LinearMap.smul_apply, smul_eq_mul, abs_of_pos hp]
        rw [inv_mul_le_iff₀ hp, mul_one]
      · have hn : P.b i < 0 := lt_of_le_of_ne (not_lt.mp hp) hb
        simp only [HPolytope.normalizeConstraints, hb, hp, if_false, LinearMap.smul_apply,
          smul_eq_mul, abs_of_neg hn]
        rw [inv_mul_le_iff₀ (neg_pos.mpr hn)]
        constructor <;> intro h <;> linarith
  have heq : ∀ i, (P.normalizeConstraints.Ae i) x = P.normalizeConstraints.be i
      ↔ (P.Ae i) x = P.be i := by
    intro i
    -- an equality row with a zero right-hand side is untouched; else divide by it
    by_cases hb : P.be i = 0
    · simp [HPolytope.normalizeConstraints, hb]
    · simp only [HPolytope.normalizeConstraints, hb, if_false, LinearMap.smul_apply,
        smul_eq_mul]
      rw [inv_mul_eq_iff_eq_mul₀ hb, mul_one]
  -- the two families of rows agree one by one
  exact and_congr (forall_congr' hle) (forall_congr' heq)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
