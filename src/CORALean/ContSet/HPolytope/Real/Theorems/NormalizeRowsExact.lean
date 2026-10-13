module

public import CORALean.ContSet.HPolytope.Real.Operations.NormalizeRows
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `normalizeRows` denotes the same set, exactly

Each nonzero row is divided on both sides by its positive 2-norm.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.normalizeRows_exact (P : HPolytope (Vec ℝ n)) :
    P.normalizeRows.construct = P.construct := by -- --- PROOF ---
  ext x
  -- one row at a time: dividing both sides by `c ≠ 0`, a norm, so `c > 0`
  have key : ∀ (c a b : ℝ), 0 < c → (c⁻¹ * a ≤ b / c ↔ a ≤ b) := by
    intro c a b hc
    rw [div_eq_inv_mul]
    exact mul_le_mul_iff_of_pos_left (inv_pos.mpr hc)
  have key' : ∀ (c a b : ℝ), 0 < c → (c⁻¹ * a = b / c ↔ a = b) := by
    intro c a b hc
    rw [div_eq_inv_mul]
    exact mul_right_inj' (inv_pos.mpr hc).ne'
  have hle : ∀ i, (P.normalizeRows.A i) x ≤ P.normalizeRows.b i ↔ (P.A i) x ≤ P.b i := by
    intro i
    -- a zero row is untouched, otherwise both sides scale by the positive norm
    by_cases h0 : _root_.Real.sqrt (∑ j, (P.A i (Pi.single j (1 : ℝ) : Vec ℝ n)) ^ 2) = 0
    · simp [HPolytope.normalizeRows, h0]
    · simp only [HPolytope.normalizeRows, h0, if_false, LinearMap.smul_apply, smul_eq_mul]
      exact key _ _ _ (lt_of_le_of_ne (_root_.Real.sqrt_nonneg _) (Ne.symm h0))
  have heq : ∀ i, (P.normalizeRows.Ae i) x = P.normalizeRows.be i ↔ (P.Ae i) x = P.be i := by
    intro i
    -- the same for an equality row
    by_cases h0 : _root_.Real.sqrt (∑ j, (P.Ae i (Pi.single j (1 : ℝ) : Vec ℝ n)) ^ 2) = 0
    · simp [HPolytope.normalizeRows, h0]
    · simp only [HPolytope.normalizeRows, h0, if_false, LinearMap.smul_apply, smul_eq_mul]
      exact key' _ _ _ (lt_of_le_of_ne (_root_.Real.sqrt_nonneg _) (Ne.symm h0))
  exact and_congr (forall_congr' hle) (forall_congr' heq)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
