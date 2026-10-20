module

public import CORALean.Specification.STL.Operations.TreeEliminateTrueFalseWith
public import CORALean.Specification.STL.Definitions.TreeWellFormed

@[expose] public section

/-!
# CORA's `eliminateTrueFalse`, as printed

`@stl/eliminateTrueFalse.m` rewrites `φ U[a,b] true` to `true`. Under `modelCheckTrace`'s reading
`φ U[a,b] true` needs `φ` on every step up to a time `t ≥ a`, at least `[0,a]`, so `false U[0,1]
true` is false. `STL.Tree.eliminateTrueFalseCora_until_counterexample` is that;
`STL.Tree.eliminateTrueFalse` keeps the node. (The rewrite of `true R[a,b] ψ` to `true` is right
under that reading.)

# CORA's `eliminateTrueFalse` of `φ U[a,b] true`

`eliminateTrueFalse(until(false, true, [0,1]))` is `true`, though `false U[0,1] true` needs
`false` at time `0` and fails on every trace. See `STL.Tree.eliminateTrueFalseCora`.

## Inputs
* `n` – state dimension
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* CORA's rewriting of until with true changes the meaning of a formula
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


variable {n : ℕ}


-- The model: CORA's code as printed, kept only to be refuted.
/-- `eliminateTrueFalse(obj)` as printed. -/
def STL.Tree.eliminateTrueFalseCora (φ : STL.Tree n) : STL.Tree n :=
  STL.Tree.eliminateTrueFalseWith (fun _ _ _ => .tt) φ

end CORALean

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
