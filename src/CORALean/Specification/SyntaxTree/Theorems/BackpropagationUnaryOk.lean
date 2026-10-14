module

public import CORALean.Specification.SyntaxTree.Operations.Backpropagation
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# What a unary `backpropagation` returns

If `backpropagation` of a unary node returns a box, its `funHan` returned an interval and the
operand returned that box.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A unary `backpropagation` that returns a box passed through its `funHan`. -/
theorem SyntaxTree.backpropagation_unary_ok {op : Unary} {w : Dom}
    {f : Dom → Dom → Outcome Dom} {t : SyntaxTree n} {v : Dom}
    {B r : Real.Interval (Vec ℝ n)} (h : backpropagation (.unary op w f t) v B = .ok r) :
    ∃ val, f v t.value = .ok val ∧ backpropagation t val B = .ok r := by -- --- PROOF ---
  simp only [backpropagation] at h
  rcases hf : f v t.value with val | _ | _
  · rw [hf] at h
    exact ⟨val, rfl, h⟩
  · rw [hf] at h; simp at h
  · rw [hf] at h; simp at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
