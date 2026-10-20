module

public import CORALean.Specification.STL.Operations.TreeCnfRewrite
public import CORALean.Specification.STL.Definitions.TreeIsCnf

@[expose] public section

/-!
# A pass that rewrites nothing leaves a conjunctive normal form

If `aux_rewrite` of `conjunctiveNormalForm.m` counts no distribution, its result is a conjunction
of clauses: no `|` is left with an `&` operand. The loop of the method stops at that pass.

## Inputs
* `φ` – formula

## Hypotheses
* `h` – the pass changes nothing

## Conclusion
* the pass result is in conjunctive normal form
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem STL.Tree.aux_isClause_of_isCnf (t : STL.Tree n) (h : t.IsCnf)
    (h' : ∀ l₁ l₂ : STL.Tree n, ¬ t = STL.Tree.and l₁ l₂) : t.IsClause := by
  cases t <;> simp_all [STL.Tree.IsCnf, STL.Tree.IsClause]

theorem STL.Tree.aux_cnfRewrite_zero (φ : STL.Tree n) : -- --- CONCL ---
    (φ.cnfRewrite).2 = 0 → (φ.cnfRewrite).1 = φ ∧ φ.IsCnf := by -- --- PROOF ---
  induction φ with
  | or φ ψ ihφ ihψ =>
    simp only [STL.Tree.cnfRewrite]
    split
    all_goals intro h
    all_goals first | omega | skip
    obtain ⟨a₁, a₂⟩ := ihφ (by omega)
    obtain ⟨b₁, b₂⟩ := ihψ (by omega)
    simp_all
    exact ⟨STL.Tree.aux_isClause_of_isCnf _ a₂ (by assumption),
      STL.Tree.aux_isClause_of_isCnf _ b₂ (by assumption)⟩
  | and φ ψ ihφ ihψ =>
    intro h
    obtain ⟨a₁, a₂⟩ := ihφ (by simp [STL.Tree.cnfRewrite] at h; omega)
    obtain ⟨b₁, b₂⟩ := ihψ (by simp [STL.Tree.cnfRewrite] at h; omega)
    simp [STL.Tree.cnfRewrite, STL.Tree.IsCnf, a₁, a₂, b₁, b₂]
  | _ => simp [STL.Tree.cnfRewrite, STL.Tree.IsCnf, STL.Tree.IsClause]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.isCnf_cnfRewrite_of_snd_eq_zero (φ : STL.Tree n) (h : (φ.cnfRewrite).2 = 0) :
    (φ.cnfRewrite).1.IsCnf := by
  obtain ⟨h₁, h₂⟩ := STL.Tree.aux_cnfRewrite_zero φ h
  rwa [h₁]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
