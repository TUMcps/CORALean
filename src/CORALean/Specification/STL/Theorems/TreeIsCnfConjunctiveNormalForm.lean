module

public import CORALean.Specification.STL.Operations.TreeCnfLoop
public import CORALean.Specification.STL.Operations.TreeCnfRewrite
public import CORALean.Specification.STL.Definitions.TreeIsCnf
public import CORALean.Specification.STL.Operations.TreeConjunctiveNormalForm

@[expose] public section

/-!
# The conjunctive normal form is a conjunction of clauses

`conjunctiveNormalForm(obj,nnf)` loops until a pass counts no distribution, and the result of such
a pass is a conjunction of clauses (`STL.Tree.aux_isCnf_cnfRewrite_of_snd_eq_zero`).

## Inputs
* `φ` – formula
* `nnf` – whether to bring the formula to negation normal form first

## Hypotheses
* none

## Conclusion
* the result is in conjunctive normal form
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


/-- A pass that rewrites nothing leaves a conjunctive normal form. -/
theorem STL.Tree.aux_isCnf_cnfRewrite_of_snd_eq_zero (φ : STL.Tree n) (h : (φ.cnfRewrite).2 = 0) :
    (φ.cnfRewrite).1.IsCnf := by
  obtain ⟨h₁, h₂⟩ := STL.Tree.aux_cnfRewrite_zero φ h
  rwa [h₁]


theorem STL.Tree.aux_isCnf_cnfLoop (φ : STL.Tree n) : -- --- CONCL ---
    φ.cnfLoop.IsCnf := by -- --- PROOF ---
  induction φ using STL.Tree.cnfLoop.induct with
  | case1 φ cnt hc =>
    rw [STL.Tree.cnfLoop, dif_pos hc]
    exact STL.Tree.aux_isCnf_cnfRewrite_of_snd_eq_zero φ hc
  | case2 φ res cnt h ih => rw [STL.Tree.cnfLoop, dif_neg h]; exact ih


-- =======================================  MAIN THEOREM  ======================================= --

/-- The result of `conjunctiveNormalForm(obj)` is a conjunction of clauses. -/
theorem STL.Tree.isCnf_conjunctiveNormalForm (φ : STL.Tree n) (nnf : Bool) :
    (φ.conjunctiveNormalForm nnf).IsCnf := STL.Tree.aux_isCnf_cnfLoop _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
