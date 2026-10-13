module

public import CORALean.ContSet.Zonotope.Real.Operations.SupportBound
public import Mathlib.Data.Real.Sign

@[expose] public section

/-!
# The support bound is the support function

`SupportBound` claims only that nothing exceeds the value, which leaves open
how much was given away. Here nothing was: picking each generator's coefficient
to be the sign of `c (Z.G j)` makes every term reach its own `|c (Z.G j)|`, so
`Z.c + Σⱼ sgn(c (Z.G j)) • Z.G j` attains the bound exactly.

Unlike an ellipsoid, no degenerate case to split on: `Real.sign 0 = 0`
contributes nothing to the witness, and `|c (Z.G j)| = 0` there too, so the
same coefficient works whether or not `c` vanishes on a generator.
-/

-- Authors:       Claude Opus 5
-- Written:       15-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.supportBound_attained (Z : Zonotope α) (c : α →ₗ[ℝ] ℝ) :
    ∃ x ∈ Z.construct, c x = (Z.supportBound c).val := by -- --- PROOF ---
  have hsign : ∀ j, Real.sign (c (Z.G j)) * c (Z.G j) = |c (Z.G j)| := fun j => by
    rcases lt_trichotomy (c (Z.G j)) 0 with h | h | h
    · rw [Real.sign_of_neg h, neg_one_mul, abs_of_neg h]
    · rw [h, Real.sign_zero, zero_mul, abs_zero]
    · rw [Real.sign_of_pos h, one_mul, abs_of_pos h]
  refine ⟨Z.c + ∑ j, Real.sign (c (Z.G j)) • Z.G j,
    ⟨fun j => Real.sign (c (Z.G j)), fun j => ?_, rfl⟩, ?_⟩
  · rcases Real.sign_apply_eq (c (Z.G j)) with h | h | h <;> simp [h]
  · show c (Z.c + ∑ j, Real.sign (c (Z.G j)) • Z.G j) = c Z.c + ∑ j, |c (Z.G j)|
    rw [map_add, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]; exact hsign j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
