module

public import CORALean.Specification.STL.Operations.TreeDesugar

@[expose] public section

/-!
# Desugaring keeps the meaning

`ξ ⊨ₜ desugar(φ) ⇔ ξ ⊨ₜ φ`: `release`, `finally`, `globally` and `next` are the `until` they are
rewritten to.

## Inputs
* `φ` – formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* desugaring keeps the meaning
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

theorem STL.Tree.sat_desugar (φ : STL.Tree NNReal ℝ n) (ξ : ℝ≥0 → Fin n → ℝ) : -- --- CONCL ---
    φ.desugar.Satisfies ξ ↔ φ.Satisfies ξ := by -- --- PROOF ---
  induction φ generalizing ξ with
  | tt | ff | cmp => rfl
  | not φ ih => simp only [STL.Tree.desugar, STL.Tree.Satisfies, ih]
  | and φ ψ ihφ ihψ => simp only [STL.Tree.desugar, STL.Tree.Satisfies, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp only [STL.Tree.desugar, STL.Tree.Satisfies, ihφ, ihψ]
  | «until» a b φ ψ ihφ ihψ =>
    simp only [STL.Tree.desugar, STL.Tree.Satisfies, STL.Tree.HasUntilWitness, ihφ, ihψ]
  | release a b φ ψ ihφ ihψ =>
    simp only [STL.Tree.desugar, STL.Tree.Satisfies, STL.Tree.HasUntilWitness, ihφ, ihψ]
  | «finally» a b φ ih => simp [STL.Tree.desugar, STL.Tree.Satisfies, STL.Tree.HasUntilWitness, ih]
  | globally a b φ ih =>
    simp only [STL.Tree.desugar, STL.Tree.Satisfies, STL.Tree.HasUntilWitness, ih]
  | next a φ ih =>
    simp only [STL.Tree.desugar, STL.Tree.Satisfies, STL.Tree.HasUntilWitness, ih]
    constructor
    · rintro ⟨t, h₁, h₂, h₃, -⟩
      obtain rfl : t = a := le_antisymm h₂ h₁
      exact h₃
    · exact fun h => ⟨a, le_rfl, le_rfl, h, fun _ _ => trivial⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
