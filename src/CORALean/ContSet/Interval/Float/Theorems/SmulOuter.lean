module

public import CORALean.ContSet.Interval.Float.Operations.Smul
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners

@[expose] public section

/-!
# `Interval.smul` over-approximates scaling every point of a box

`Interval.mul_between_corners` at every entry, `[cLo, cHi]` standing in for a
scalar known only to lie in that range rather than an exact one.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.smul_outer {cLo cHi : 𝕋} {c : ℝ} (hcLo : toReal cLo ≤ c)
    (hcHi : c ≤ toReal cHi) (I : Interval (Mat 𝕋 m n)) {v : Mat ℝ m n} (hv : v ∈ I.construct) :
    c • v ∈ (Interval.smul cLo cHi I).construct := by -- --- PROOF ---
  intro q
  obtain ⟨i, j⟩ := q
  have hv' := hv (i, j)
  simp only [Entrywise.entry_mat] at hv' ⊢
  rw [Matrix.smul_apply, smul_eq_mul]
  exact Interval.mul_between_corners hcLo hcHi hv'.1 hv'.2

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
