module

public import CORALean.Specification.STL.Operations.TreeCnfRewrite

@[expose] public section

/-!
# One CNF pass keeps the meaning

A pass of `conjunctiveNormalForm.m`'s `aux_rewrite` returns a formula satisfied by the same
traces: distributing `|` over `&` is a propositional equivalence.
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

theorem STL.Tree.sat_cnfRewrite (φ : STL.Tree n) (ξ : ℝ≥0 → Fin n → ℝ) :
    (φ.cnfRewrite).1.Sat ξ ↔ φ.Sat ξ := by -- --- PROOF ---
  induction φ generalizing ξ with
  | or φ ψ ihφ ihψ =>
    simp only [STL.Tree.cnfRewrite]
    split <;> (have e₁ := ihφ ξ; have e₂ := ihψ ξ; simp_all only [STL.Tree.Sat] <;> grind)
  | and φ ψ ihφ ihψ => simp [STL.Tree.cnfRewrite, STL.Tree.Sat, ihφ, ihψ]
  | _ => simp [STL.Tree.cnfRewrite]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
