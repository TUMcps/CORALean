module

public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Definitions.DomWithin
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree

@[expose] public section

/-!
# Meeting an interval with extended bounds

`intPrev & interval(lo,hi)` with bounds in `EReal` (`restrict`) holds `s`, and lies inside
`intPrev`, when
`intPrev` holds `s` and `lo ≤ s ≤ hi`.

## Inputs
* `e` – extended real
* `a` – lower bound
* `b` – upper bound

## Hypotheses
* `h₁` – the lower bound is at most the extended real
* `h₂` – the extended real is at most the upper bound

## Conclusion
* the real part lies between the bounds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A real between two coerced reals has a finite real part between them. -/
private theorem SyntaxTree.toReal_between {e : EReal} {a b : ℝ} (h₁ : (a : EReal) ≤ e) (h₂ : e ≤ b)
    :
    a ≤ e.toReal ∧ e.toReal ≤ b := by
  have hb : e ≠ ⊥ := fun h => by simp [h, EReal.coe_ne_bot] at h₁
  have ht : e ≠ ⊤ := fun h => by simp [h] at h₂
  rw [← EReal.coe_toReal ht hb] at h₁ h₂
  exact ⟨EReal.coe_le_coe_iff.1 h₁, EReal.coe_le_coe_iff.1 h₂⟩

/-- `restrict prev lo hi` holds `s` and lies inside `prev`. -/
theorem SyntaxTree.restrict_contains {prev : Dom} {lo hi : EReal} {s : ℝ}
    (hs : Dom.contains prev s) (h₁ : lo ≤ s) (h₂ : (s : EReal) ≤ hi) :
    Dom.contains (restrict prev lo hi) s ∧ Dom.within (restrict prev lo hi)
      prev := by -- --- PROOF ---
  have hb : hi ≠ ⊥ := fun h => by simp [h] at h₂
  have hl : (max (prev.inf 0 : EReal) lo).toReal ≥ prev.inf 0 ∧
      (max (prev.inf 0 : EReal) lo).toReal ≤ s :=
    toReal_between (le_max_left _ _) (max_le (EReal.coe_le_coe_iff.2 hs.1) h₁)
  have hu : prev.sup 0 ≥ (min (prev.sup 0 : EReal) hi).toReal ∧
      s ≤ (min (prev.sup 0 : EReal) hi).toReal :=
    ⟨(toReal_between (a := s) (le_min (EReal.coe_le_coe_iff.2 hs.2) h₂) (min_le_left _ _)).2,
      (toReal_between (a := s) (le_min (EReal.coe_le_coe_iff.2 hs.2) h₂) (min_le_left _ _)).1⟩
  simp only [restrict, Dom.contains, Dom.within, hb, if_false]
  exact ⟨⟨hl.2, hu.2⟩, hl.1, hu.1⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
