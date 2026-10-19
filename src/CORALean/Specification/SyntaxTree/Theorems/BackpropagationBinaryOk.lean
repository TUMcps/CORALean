module

public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Operations.Backpropagation
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# What a binary `backpropagation` returns

If `backpropagation` of a binary node returns a box, its first operand returned one that holds
every point of it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A binary `backpropagation` that returns a box passed through its first operand. -/
theorem SyntaxTree.backpropagation_binary_ok {op : Binary} {w : Dom}
    {f : Dom → Dom → Dom → Pair} {t₁ t₂ : SyntaxTree n} {v : Dom}
    {B r : Real.Interval (Vec ℝ n)}
    (h : backpropagation (.binary op w f t₁ t₂) v B = .ok r) : -- --- CONCL ---
    ∃ r₁, backpropagation t₁ (f v t₁.value t₂.value).left B = .ok r₁ ∧
      ∀ x, InBox r x → InBox r₁ x := by -- --- PROOF ---
  simp only [backpropagation] at h
  rcases h₁ : backpropagation t₁ (f v t₁.value t₂.value).left B with r₁ | _ | _
  · refine ⟨r₁, rfl, fun x hx i => ?_⟩
    rw [h₁] at h
    simp only at h
    rcases h₂ : backpropagation t₂ (f v t₁.value t₂.value).right B with r₂ | _ | _
    · rw [h₂] at h
      simp only [Outcome.ok.injEq] at h
      subst h
      exact ⟨(le_max_left _ _).trans (hx i).1, (hx i).2.trans (min_le_left _ _)⟩
    · rw [h₂] at h; simp at h
    · rw [h₂] at h; simp at h
  · rw [h₁] at h; simp at h
  · rw [h₁] at h; simp at h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
