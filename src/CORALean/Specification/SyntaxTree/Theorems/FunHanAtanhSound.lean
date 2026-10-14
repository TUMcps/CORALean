module

public import CORALean.ContSet.Interval.Real.Operations.Atanh
public import CORALean.Specification.SyntaxTree.Definitions.UnarySound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.MeetContains

@[expose] public section

/-!
# `aaux_tanh_` is sound

`aaux_tanh_` keeps every solution of `atanh s ∈ int` for `s` in `(-1,1)`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `tanh` is monotone. -/
private theorem SyntaxTree.tanh_mono : Monotone Real.tanh := by -- --- PROOF ---
  refine StrictMono.monotone fun a b hab => ?_
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    div_lt_div_iff₀ (Real.cosh_pos a) (Real.cosh_pos b)]
  have h : 0 < Real.sinh (b - a) := Real.sinh_pos_iff.2 (sub_pos.2 hab)
  rw [Real.sinh_sub] at h
  linarith

/-- `aaux_tanh_` is sound for `atanh` on an operand inside `(-1,1)`. -/
theorem SyntaxTree.funHanAtanh_sound (prev : Dom) (hd₁ : -1 < prev.inf 0) (hd₂ : prev.sup 0 < 1) :
    UnarySound Unary.atanh.fn prev (Real.Interval.atanh prev) funHanAtanh := by -- --- PROOF ---
  intro int _ s hs hi
  have h : int.inf 0 ≤ Real.artanh s ∧ Real.artanh s ≤ int.sup 0 := hi
  have hs1 : -1 < s := hd₁.trans_le hs.1
  have hs2 : s < 1 := hs.2.trans_lt hd₂
  have e : Real.tanh (Real.artanh s) = s := Real.tanh_artanh ⟨hs1, hs2⟩
  have l₁ : Real.tanh (int.inf 0) ≤ s := by
    rw [← e]; exact tanh_mono h.1
  have l₂ : s ≤ Real.tanh (int.sup 0) := by
    rw [← e]; exact tanh_mono h.2
  obtain ⟨h₁, h₂⟩ := meet_contains hs ((min_le_left _ _).trans l₁) (l₂.trans (le_max_right _ _))
  exact ⟨_, rfl, h₁, h₂⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
