module

public import CORALean.Specification.STL.Operations.TreeGetVariables
public import CORALean.Specification.STL.Theorems.ExprEvalCongrVariables

@[expose] public section

/-!
# A formula reads only its variables

Whether a trace satisfies a formula depends on the variables `getVariables` lists alone: two
traces that agree on them at every time are satisfying together.

## Inputs
* `φ` – formula
* `ξ` – trace
* `ξ'` – second trace

## Hypotheses
* `h` – the traces agree on the formula's variables

## Conclusion
* the formula holds on both or neither
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

theorem STL.Tree.sat_congr_getVariables (φ : STL.Tree n) (ξ ξ' : ℝ≥0 → Fin n → ℝ)
    (h : ∀ t, ∀ i ∈ φ.getVariables, ξ t i = ξ' t i) : -- --- CONCL ---
    φ.Sat ξ ↔ φ.Sat ξ' := by -- --- PROOF ---
  induction φ generalizing ξ ξ' with
  | tt | ff => rfl
  -- a comparison reads its expressions at time `0`
  | cmp op e₁ e₂ =>
    simp only [STL.Tree.Sat, STL.Expr.eval_congr_variables e₁ (fun i hi => h 0 i
      (by simp [STL.Tree.getVariables, hi])), STL.Expr.eval_congr_variables e₂ (fun i hi => h 0 i
      (by simp [STL.Tree.getVariables, hi]))]
  | not φ ih => simp only [STL.Tree.Sat, ih ξ ξ' h]
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [STL.Tree.Sat, ihφ ξ ξ' fun t i hi => h t i (by simp [STL.Tree.getVariables, hi]),
      ihψ ξ ξ' fun t i hi => h t i (by simp [STL.Tree.getVariables, hi])]
  -- the temporal operators read the operands at shifted traces
  | «until» a b φ ψ ihφ ihψ | release a b φ ψ ihφ ihψ =>
    have hφ : ∀ t, φ.Sat (Time.shift ξ t) ↔ φ.Sat (Time.shift ξ' t) := fun t =>
      ihφ _ _ fun s i hi => h _ i (by simp [STL.Tree.getVariables, hi])
    have hψ : ∀ t, ψ.Sat (Time.shift ξ t) ↔ ψ.Sat (Time.shift ξ' t) := fun t =>
      ihψ _ _ fun s i hi => h _ i (by simp [STL.Tree.getVariables, hi])
    simp only [STL.Tree.Sat, STL.Tree.HasUntilWitness, hφ, hψ]
  | «finally» a b φ ih | globally a b φ ih =>
    have hφ : ∀ t, φ.Sat (Time.shift ξ t) ↔ φ.Sat (Time.shift ξ' t) := fun t =>
      ih _ _ fun s i hi => h _ i (by simpa [STL.Tree.getVariables] using hi)
    simp only [STL.Tree.Sat, STL.Tree.HasUntilWitness, hφ]
  | next a φ ih => exact ih _ _ fun s i hi => h _ i (by simpa [STL.Tree.getVariables] using hi)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
