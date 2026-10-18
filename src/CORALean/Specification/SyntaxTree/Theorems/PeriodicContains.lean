module

public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Definitions.DomWithin
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.Specification.SyntaxTree.Theorems.MeetContains

@[expose] public section

/-!
# The periodic tail keeps a solution

If `s` lies in `intPrev` and in one of the two branches shifted by `2 pi k`, `aux_periodic_` holds
`s`:
the shifted copies nearest to `intPrev`'s ends are the largest and the smallest solution, or
`intPrev`'s
end itself where a copy contains it.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A copy of a branch below `b` is below `b`, or contains it. -/
private theorem SyntaxTree.periodic_branch_upper {p b i s' s : ℝ} (hp : 0 < p) (hsb : s ≤ b) (k : ℤ)
    (h₁ : i + k * p ≤ s) (h₂ : s ≤ s' + k * p) :
    (i + (⌈(b - s') / p⌉ : ℝ) * p ≤ b ∧ b ≤ s' + (⌈(b - s') / p⌉ : ℝ) * p) ∨
      s ≤ s' + ((⌈(b - s') / p⌉ : ℝ) - 1) * p := by -- --- PROOF ---
  have c := Int.le_ceil ((b - s') / p)
  rw [div_le_iff₀ hp] at c
  by_cases hk : ⌈(b - s') / p⌉ ≤ k
  · -- `k` reaches `b`: `b` is inside this copy
    have hk' : (⌈(b - s') / p⌉ : ℝ) ≤ k := by exact_mod_cast hk
    exact Or.inl ⟨by nlinarith, by linarith⟩
  · have hk' : (k : ℝ) ≤ (⌈(b - s') / p⌉ : ℝ) - 1 := by
      have : k ≤ ⌈(b - s') / p⌉ - 1 := by omega
      exact_mod_cast this
    exact Or.inr (by nlinarith)

/-- A copy of a branch above `a` is above `a`, or contains it. -/
private theorem SyntaxTree.periodic_branch_lower {p a i s' s : ℝ} (hp : 0 < p) (has : a ≤ s) (k : ℤ)
    (h₁ : i + k * p ≤ s) (h₂ : s ≤ s' + k * p) :
    (i + (⌊(a - i) / p⌋ : ℝ) * p ≤ a ∧ a ≤ s' + (⌊(a - i) / p⌋ : ℝ) * p) ∨
      i + ((⌊(a - i) / p⌋ : ℝ) + 1) * p ≤ s := by -- --- PROOF ---
  have c := Int.floor_le ((a - i) / p)
  rw [le_div_iff₀ hp] at c
  by_cases hk : k ≤ ⌊(a - i) / p⌋
  · -- `k` stays below `a`: `a` is inside this copy
    have hk' : (k : ℝ) ≤ (⌊(a - i) / p⌋ : ℝ) := by exact_mod_cast hk
    exact Or.inl ⟨by linarith, by nlinarith⟩
  · have hk' : (⌊(a - i) / p⌋ : ℝ) + 1 ≤ k := by
      have : ⌊(a - i) / p⌋ + 1 ≤ k := by omega
      exact_mod_cast this
    exact Or.inr (by nlinarith)

/-- `aux_periodic_` holds `s` if `s` lies in a shifted branch and in `intPrev`. -/
theorem SyntaxTree.periodic_contains {R₁ R₂ prev : Dom} {s : ℝ} (hs : Dom.contains prev s) (k : ℤ)
    (hk : (R₁.inf 0 + k * (2 * Real.pi) ≤ s ∧ s ≤ R₁.sup 0 + k * (2 * Real.pi)) ∨
      (R₂.inf 0 + k * (2 * Real.pi) ≤ s ∧ s ≤ R₂.sup 0 + k * (2 * Real.pi))) : -- --- STMT ---
    Dom.contains (periodic R₁ R₂ prev) s ∧ Dom.within (periodic R₁ R₂ prev)
      prev := by -- --- PROOF ---
  have hp : 0 < 2 * Real.pi := by positivity
  have lowerK : (R₁.inf 0 + (⌊(prev.inf 0 - R₁.inf 0) / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤
        prev.inf 0 ∧ prev.inf 0 ≤ R₁.sup 0 +
          (⌊(prev.inf 0 - R₁.inf 0) / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)) ∨
      (R₂.inf 0 + (⌊(prev.inf 0 - R₂.inf 0) / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤
        prev.inf 0 ∧ prev.inf 0 ≤ R₂.sup 0 +
          (⌊(prev.inf 0 - R₂.inf 0) / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)) ∨
      R₁.inf 0 + ((⌊(prev.inf 0 - R₁.inf 0) / (2 * Real.pi)⌋ : ℝ) + 1) * (2 * Real.pi) ≤ s ∨
      R₂.inf 0 + ((⌊(prev.inf 0 - R₂.inf 0) / (2 * Real.pi)⌋ : ℝ) + 1) * (2 * Real.pi) ≤ s := by
    rcases hk with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rcases periodic_branch_lower hp hs.1 k h₁ h₂ with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
    · rcases periodic_branch_lower hp hs.1 k h₁ h₂ with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
  -- the fact `(R₁.inf 0 + (⌈(prev.sup 0 - R₁.sup 0) / (2 * Real.pi)⌉ : ℝ) * …`
  have upperK : (R₁.inf 0 + (⌈(prev.sup 0 - R₁.sup 0) / (2 * Real.pi)⌉ : ℝ) * (2 * Real.pi) ≤
        prev.sup 0 ∧ prev.sup 0 ≤ R₁.sup 0 +
          (⌈(prev.sup 0 - R₁.sup 0) / (2 * Real.pi)⌉ : ℝ) * (2 * Real.pi)) ∨
      (R₂.inf 0 + (⌈(prev.sup 0 - R₂.sup 0) / (2 * Real.pi)⌉ : ℝ) * (2 * Real.pi) ≤
        prev.sup 0 ∧ prev.sup 0 ≤ R₂.sup 0 +
          (⌈(prev.sup 0 - R₂.sup 0) / (2 * Real.pi)⌉ : ℝ) * (2 * Real.pi)) ∨
      s ≤ R₁.sup 0 + ((⌈(prev.sup 0 - R₁.sup 0) / (2 * Real.pi)⌉ : ℝ) - 1) * (2 * Real.pi) ∨
      s ≤ R₂.sup 0 + ((⌈(prev.sup 0 - R₂.sup 0) / (2 * Real.pi)⌉ : ℝ) - 1) * (2 * Real.pi) := by
    -- take apart the hypothesis
    rcases hk with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rcases periodic_branch_upper hp hs.2 k h₁ h₂ with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
    · rcases periodic_branch_upper hp hs.2 k h₁ h₂ with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
  unfold periodic
  dsimp only
  refine meet_contains hs ?_ ?_
  · -- the new lower bound is at most `s`
    split_ifs with h h'
    · exact hs.1
    · rcases lowerK with h1 | h1 | h1 | h1
      · exact absurd (Or.inl h1) h
      · exact absurd (Or.inr h1) h
      · linarith
      · linarith
    · rcases lowerK with h1 | h1 | h1 | h1
      · exact absurd (Or.inl h1) h
      · exact absurd (Or.inr h1) h
      · linarith
      · linarith
  · -- the new upper bound is at least `s`
    split_ifs with h h'
    · exact hs.2
    · rcases upperK with h1 | h1 | h1 | h1
      · exact absurd (Or.inl h1) h
      · exact absurd (Or.inr h1) h
      · linarith
      · linarith
    · rcases upperK with h1 | h1 | h1 | h1
      · exact absurd (Or.inl h1) h
      · exact absurd (Or.inr h1) h
      · linarith
      · linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
