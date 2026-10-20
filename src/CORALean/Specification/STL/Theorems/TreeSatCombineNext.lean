module

public import CORALean.Specification.STL.Operations.TreeCombineNext
public import CORALean.Specification.STL.Theorems.ShiftShift

@[expose] public section

/-!
# Moving next inwards keeps the meaning

`combineNext(obj)` is satisfied by the same traces as `obj`: `next` distributes over `&`, `|` and
`~`, and two nested `next` add their times.

## Inputs
* `φ` – formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* moving next inwards keeps the meaning
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

theorem STL.Tree.sat_combineNext (φ : STL.Tree n) (ξ : ℝ≥0 → Fin n → ℝ) : -- --- CONCL ---
    φ.combineNext.Sat ξ ↔ φ.Sat ξ := by -- --- PROOF ---
  induction φ using STL.Tree.combineNext.induct generalizing ξ with
  | case1 a φ ψ h ihφ ihψ =>
    simp only [STL.Tree.combineNext, h, ↓reduceIte, STL.Tree.Sat, ihφ ξ, ihψ ξ]
  | case2 a φ ψ h => simp [STL.Tree.combineNext, h]
  | case3 a φ ψ h ihφ ihψ =>
    simp only [STL.Tree.combineNext, h, ↓reduceIte, STL.Tree.Sat, ihφ ξ, ihψ ξ]
  | case4 a φ ψ h => simp [STL.Tree.combineNext, h]
  | case5 a φ ih => simp only [STL.Tree.combineNext, STL.Tree.Sat, ih ξ]
  | case6 a b φ ih =>
    rw [STL.Tree.combineNext, ih ξ]
    simp only [STL.Tree.Sat]
    rw [Time.shift_shift, add_comm b a]
  | case7 a φ h₁ h₂ h₃ h₄ => rw [STL.Tree.combineNext] <;> assumption
  | case8 φ ψ ihφ ihψ => simp only [STL.Tree.combineNext, STL.Tree.Sat, ihφ ξ, ihψ ξ]
  | case9 φ ψ ihφ ihψ => simp only [STL.Tree.combineNext, STL.Tree.Sat, ihφ ξ, ihψ ξ]
  | case10 φ ih => simp only [STL.Tree.combineNext, STL.Tree.Sat, ih ξ]
  | case11 φ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ => rw [STL.Tree.combineNext] <;> assumption

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
