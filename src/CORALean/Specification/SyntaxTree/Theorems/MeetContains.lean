module

public import CORALean.ContSet.Interval.Real.Operations.Intersection
public import CORALean.Specification.SyntaxTree.Definitions.Basic
public import CORALean.Specification.SyntaxTree.Definitions.DomWithin
public import CORALean.Specification.SyntaxTree.Operations.Basic
public import CORALean.Specification.SyntaxTree.SyntaxTree
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# Meeting an interval with one that holds the point

`intPrev & interval(lo,hi)` holds `s` and lies inside `intPrev` when `intPrev` holds `s` and `lo ≤
s ≤ hi`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ} {B : Real.Interval (Vec ℝ n)} {t : SyntaxTree n}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `prev & interval(lo,hi)` holds `s` and lies inside `prev`. -/
theorem SyntaxTree.meet_contains {prev : Dom} {lo hi s : ℝ} (hs : Dom.contains prev s)
    (h₁ : lo ≤ s) (h₂ : s ≤ hi) :
    Dom.contains (Real.Interval.intersection prev (interval lo hi)) s ∧
      Dom.within (Real.Interval.intersection prev (interval lo hi)) prev :=
  ⟨⟨max_le hs.1 h₁, le_min hs.2 h₂⟩, le_max_left _ _, min_le_left _ _⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
