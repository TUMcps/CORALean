module

public import CORALean.ContSet.Interval.Real.Operations.Atan
public import CORALean.ContSet.Interval.Real.Operations.Tan
public import CORALean.Specification.SyntaxTree.Definitions.UnarySound
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.PeriodicContains

@[expose] public section

/-!
# `aux_tan_` is sound

`aux_tan_` (without the cut to `[-1,1]`) keeps every solution of `tan s ∈ int` for `s` in `(-pi/2,
pi/2)`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `aux_tan_` is sound for `tan` on an operand inside `(-pi/2, pi/2)`. -/
theorem SyntaxTree.tan_sound (prev : Dom) (hd₁ : -(Real.pi / 2) < prev.inf 0)
    (hd₂ : prev.sup 0 < Real.pi / 2) :
    UnarySound Unary.tan.fn prev (Real.Interval.tan prev) funHanTan := by -- --- PROOF ---
  intro int _ s hs hi
  have h : int.inf 0 ≤ Real.tan s ∧ Real.tan s ≤ int.sup 0 := hi
  have e : Real.arctan (Real.tan s) = s :=
    Real.arctan_tan (hd₁.trans_le hs.1) (hs.2.trans_lt hd₂)
  have a₁ : Real.arctan (int.inf 0) ≤ s := by
    rw [← e]; exact Real.arctan_strictMono.monotone h.1
  have a₂ : s ≤ Real.arctan (int.sup 0) := by
    rw [← e]; exact Real.arctan_strictMono.monotone h.2
  obtain ⟨c, w⟩ := periodic_contains (R₁ := Real.Interval.atan int)
    (R₂ := interval ((Real.Interval.atan int).inf 0 + Real.pi) ((Real.Interval.atan int).sup 0 +
        Real.pi))
    hs 0 (Or.inl ⟨by simpa [Real.Interval.atan] using a₁, by simpa [Real.Interval.atan] using a₂⟩)
  exact ⟨_, rfl, c, w⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
