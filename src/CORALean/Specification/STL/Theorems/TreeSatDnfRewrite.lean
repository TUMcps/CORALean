module

public import CORALean.Specification.STL.Operations.TreeDnfRewrite

@[expose] public section

/-!
# One DNF pass keeps the meaning

A pass of `disjunctiveNormalForm.m`'s `aux_rewrite` returns a formula satisfied by the same
traces: distributing `&` over `|` is a propositional equivalence.

## Inputs
* `φ` – formula
* `ξ` – trace

## Hypotheses
* none

## Conclusion
* one pass keeps the meaning
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

theorem STL.Tree.sat_dnfRewrite (φ : STL.Tree n) (ξ : ℝ≥0 → Fin n → ℝ) : -- --- CONCL ---
    (φ.dnfRewrite).1.Sat ξ ↔ φ.Sat ξ := by -- --- PROOF ---
  induction φ generalizing ξ with
  | and φ ψ ihφ ihψ =>
    simp only [STL.Tree.dnfRewrite]
    split <;> (have e₁ := ihφ ξ; have e₂ := ihψ ξ; simp_all only [STL.Tree.Sat] <;> grind)
  | or φ ψ ihφ ihψ => simp [STL.Tree.dnfRewrite, STL.Tree.Sat, ihφ, ihψ]
  | _ => simp [STL.Tree.dnfRewrite]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
