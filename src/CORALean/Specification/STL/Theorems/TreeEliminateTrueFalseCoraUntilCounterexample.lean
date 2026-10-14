module

public import CORALean.Specification.STL.Operations.TreeEliminateTrueFalseCora
public import CORALean.Specification.STL.Definitions.TreeWellFormed

@[expose] public section

/-!
# CORA's `eliminateTrueFalse` of `φ U[a,b] true`

`eliminateTrueFalse(until(false, true, [0,1]))` is `true`, though `false U[0,1] true` needs
`false` at time `0` and fails on every trace. See `STL.Tree.eliminateTrueFalseCora`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.eliminateTrueFalseCora_until_counterexample (n : ℕ) (ξ : ℝ≥0 → Fin n → ℝ) :
    ∃ φ : STL.Tree n, φ.WellFormed ∧ ¬ (φ.eliminateTrueFalseCora.Sat ξ ↔ φ.Sat ξ) := by
  refine ⟨.until 0 1 .ff .tt, ⟨zero_le_one, trivial, trivial⟩, fun h => ?_⟩
  obtain ⟨t, -, -, -, h₄⟩ := h.1 (by simp [STL.Tree.eliminateTrueFalseCora,
    STL.Tree.eliminateTrueFalseWith, STL.Tree.Sat])
  exact h₄ 0 (by simp)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
