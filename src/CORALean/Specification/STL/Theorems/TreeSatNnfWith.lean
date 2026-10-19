module

public import CORALean.Specification.STL.Operations.TreeNnfWith

@[expose] public section

/-!
# Negation normal form, for a correct negation of the comparisons

If `ng` negates a comparison (`ng op` holds where `op` does not), `aux_recursive(obj,neg)` returns
a formula satisfied exactly when `obj` is (`neg = false`) or is not (`neg = true`).
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
    (hng : ∀ op a b, (ng op).rel a b ↔ ¬ op.rel a b) (φ : STL.Tree n) (neg : Bool)
    (ξ : ℝ≥0 → Fin n → ℝ) :
    (φ.nnfWith ng neg).Sat ξ ↔ (φ.Sat ξ ↔ neg = false) := by -- --- PROOF ---
  induction φ generalizing neg ξ with
  | tt => cases neg <;> simp [STL.Tree.nnfWith, STL.Tree.Sat]
  | ff => cases neg <;> simp [STL.Tree.nnfWith, STL.Tree.Sat]
  | cmp op e₁ e₂ => cases neg <;> simp [STL.Tree.nnfWith, STL.Tree.Sat, hng]
  | not φ ih => cases neg <;> simp [STL.Tree.nnfWith, STL.Tree.Sat, ih]
  | and φ ψ ihφ ihψ =>
    cases neg <;> simp [STL.Tree.nnfWith, STL.Tree.Sat, ihφ, ihψ, imp_iff_not_or]
  | or φ ψ ihφ ihψ => cases neg <;> simp [STL.Tree.nnfWith, STL.Tree.Sat, ihφ, ihψ]
  | «until» a b φ ψ ihφ ihψ => cases neg <;>
    simp [STL.Tree.nnfWith, STL.Tree.Sat, STL.Tree.HasUntilWitness, ihφ, ihψ]
  | release a b φ ψ ihφ ihψ => cases neg <;>
    simp [STL.Tree.nnfWith, STL.Tree.Sat, STL.Tree.HasUntilWitness, ihφ, ihψ]
  | «finally» a b φ ih => cases neg <;>
    simp [STL.Tree.nnfWith, STL.Tree.Sat,
      STL.Tree.HasUntilWitness, ih]
  | globally a b φ ih => cases neg <;>
    simp [STL.Tree.nnfWith, STL.Tree.Sat,
      STL.Tree.HasUntilWitness, ih]
  | next a φ ih => cases neg <;> simp [STL.Tree.nnfWith, STL.Tree.Sat, ih]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
