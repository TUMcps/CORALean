module

public import CORALean.ContSet.Interval.Real.Operations.Atan
public import CORALean.Specification.SyntaxTree.Definitions.UnarySound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.RestrictContains

@[expose] public section

/-!
# `aaux_tan_` is sound

`aaux_tan_` keeps every solution of `atan s ∈ int`; `tan(±pi/2) = ±Inf` is the extended bound.

## Inputs
* `prev` – previous interval

## Hypotheses
* none

## Conclusion
* the inverse of the inverse tangent keeps every solution
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aaux_tan_` is sound for `atan`. -/
theorem SyntaxTree.funHanAtan_sound (prev : Dom) : -- --- CONCL ---
    UnarySound Unary.atan.fn prev (Real.Interval.atan prev) funHanAtan := by -- --- PROOF ---
  intro int hw s hs hi
  have h : int.inf 0 ≤ Real.arctan s ∧ Real.arctan s ≤ int.sup 0 := hi
  have hlo : -(Real.pi / 2) < int.inf 0 := (Real.neg_pi_div_two_lt_arctan _).trans_le hw.1
  have hsup : int.sup 0 < Real.pi / 2 := hw.2.trans_lt (Real.arctan_lt_pi_div_two _)
  have hnd : ¬ int.sup 0 < -(Real.pi / 2) := not_lt.2 (hlo.le.trans (h.1.trans h.2))
  have e : Real.tan (Real.arctan s) = s := Real.tan_arctan s
  unfold funHanAtan
  have hi₂ : int.inf 0 ≠ Real.pi / 2 :=
    (h.1.trans_lt (Real.arctan_lt_pi_div_two _)).ne
  have hs₁ : int.sup 0 ≠ -(Real.pi / 2) :=
    ((Real.neg_pi_div_two_lt_arctan _).trans_le h.2).ne'
  -- unfold the definitions
  simp only [not_lt.2 hlo.le, hnd, if_false, hlo.ne', hi₂, hs₁, hsup.ne]
  have l₁ : Real.tan (int.inf 0) ≤ s := by
    rw [← e]
    exact (Real.strictMonoOn_tan.le_iff_le ⟨hlo, h.1.trans_lt (Real.arctan_lt_pi_div_two _)⟩
      ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩).2 h.1
  have l₂ : s ≤ Real.tan (int.sup 0) := by
    rw [← e]
    exact (Real.strictMonoOn_tan.le_iff_le ⟨Real.neg_pi_div_two_lt_arctan _,
      Real.arctan_lt_pi_div_two _⟩ ⟨(Real.neg_pi_div_two_lt_arctan _).trans_le h.2, hsup⟩).2 h.2
  obtain ⟨c, w⟩ := restrict_contains hs (lo := min _ _) (hi := max _ _)
    ((min_le_left _ _).trans (EReal.coe_le_coe_iff.2 l₁))
    ((EReal.coe_le_coe_iff.2 l₂).trans (le_max_right _ _))
  exact ⟨_, rfl, c, w⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
