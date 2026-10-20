module

public import CORALean.Specification.STL.Operations.TreeCombineNext
public import CORALean.Specification.STL.Definitions.TreeIsNextCombined

@[expose] public section

/-!
# combineNext leaves no next to move

The result of `combineNext(obj)` is combined: no `next` is left over a `~`, over another `next`,
or over an `&` or `|` with a temporal operand.

## Inputs
* `φ` – formula

## Hypotheses
* none

## Conclusion
* no next operator is left to move
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.isNextCombined_combineNext (φ : STL.Tree n) : -- --- CONCL ---
    φ.combineNext.IsNextCombined := by -- --- PROOF ---
  induction φ using STL.Tree.combineNext.induct with
  | case1 a φ ψ h ihφ ihψ | case3 a φ ψ h ihφ ihψ =>
    simp only [STL.Tree.combineNext, h, ↓reduceIte, STL.Tree.IsNextCombined]
    exact ⟨ihφ, ihψ⟩
  | case2 a φ ψ h | case4 a φ ψ h =>
    rw [STL.Tree.combineNext, if_neg h]
    simpa [STL.Tree.IsNextCombined, STL.Tree.temporal] using h
  | case5 a φ ih => rw [STL.Tree.combineNext]; exact ih
  | case6 a b φ ih => rw [STL.Tree.combineNext]; exact ih
  | case7 a φ h₁ h₂ h₃ h₄ =>
    rw [STL.Tree.combineNext] <;> try assumption
    cases φ <;> simp_all [STL.Tree.IsNextCombined]
  | case8 φ ψ ihφ ihψ | case9 φ ψ ihφ ihψ =>
    simp only [STL.Tree.combineNext, STL.Tree.IsNextCombined]
    exact ⟨ihφ, ihψ⟩
  | case10 φ ih => simp only [STL.Tree.combineNext, STL.Tree.IsNextCombined]; exact ih
  | case11 φ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ =>
    rw [STL.Tree.combineNext] <;> try assumption
    cases φ <;> simp_all [STL.Tree.IsNextCombined]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
