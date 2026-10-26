module

public import CORALean.Specification.STL.Operations.TreeNnfWith

@[expose] public section

/-!
# Negation normal form, for a correct negation of the comparisons

If `ng` negates a comparison (`ng op` holds where `op` does not), `aux_recursive(obj,neg)` returns
a formula satisfied exactly when `obj` is (`neg = false`) or is not (`neg = true`).

## Inputs
* `ng` – negation of a comparison
* `φ` – formula
* `neg` – negate the formula
* `ξ` – trace

## Hypotheses
* `hng` – the function negates comparisons correctly

## Conclusion
* the result holds iff the formula holds or fails as requested
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal


variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.sat_nnfWith (ng : STL.Cmp → STL.Cmp)
    (hng : ∀ op a b, (ng op).Relates a b ↔ ¬ op.Relates a b) (φ : STL.Tree NNReal ℝ n) (neg : Bool)
    (ξ : ℝ≥0 → Fin n → ℝ) : -- --- CONCL ---
    (φ.nnfWith ng neg).Satisfies ξ ↔ (φ.Satisfies ξ ↔ neg = false) := by -- --- PROOF ---
  induction φ generalizing neg ξ with
  | tt => cases neg <;> simp [STL.Tree.nnfWith, STL.Tree.Satisfies]
  | ff => cases neg <;> simp [STL.Tree.nnfWith, STL.Tree.Satisfies]
  | cmp op e₁ e₂ => cases neg <;> simp [STL.Tree.nnfWith, STL.Tree.Satisfies, hng]
  | not φ ih => cases neg <;> simp [STL.Tree.nnfWith, STL.Tree.Satisfies, ih]
  | and φ ψ ihφ ihψ =>
    cases neg <;> simp [STL.Tree.nnfWith, STL.Tree.Satisfies, ihφ, ihψ, imp_iff_not_or]
  | or φ ψ ihφ ihψ => cases neg <;> simp [STL.Tree.nnfWith, STL.Tree.Satisfies, ihφ, ihψ]
  | «until» a b φ ψ ihφ ihψ => cases neg <;>
    simp [STL.Tree.nnfWith, STL.Tree.Satisfies, STL.Tree.HasUntilWitness, ihφ, ihψ]
  | release a b φ ψ ihφ ihψ => cases neg <;>
    simp [STL.Tree.nnfWith, STL.Tree.Satisfies, STL.Tree.HasUntilWitness, ihφ, ihψ]
  | «finally» a b φ ih => cases neg <;>
    simp [STL.Tree.nnfWith, STL.Tree.Satisfies,
      STL.Tree.HasUntilWitness, ih]
  | globally a b φ ih => cases neg <;>
    simp [STL.Tree.nnfWith, STL.Tree.Satisfies,
      STL.Tree.HasUntilWitness, ih]
  | next a φ ih => cases neg <;> simp [STL.Tree.nnfWith, STL.Tree.Satisfies, ih]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
