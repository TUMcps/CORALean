module

public import CORALean.Specification.STL.Operations.TreeDnfRewrite
public import CORALean.Specification.STL.Definitions.TreeIsDnf

@[expose] public section

/-!
# A pass that rewrites nothing leaves a disjunctive normal form

If `aux_rewrite` of `disjunctiveNormalForm.m` counts no distribution, its result is a disjunction
of cubes: no `&` is left with an `|` operand. The loop of the method stops at that pass.
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

theorem STL.Tree.aux_isCube_of_isDnf (t : STL.Tree n) (h : t.IsDnf)
    (h' : ∀ l₁ l₂ : STL.Tree n, ¬ t = STL.Tree.or l₁ l₂) : t.IsCube := by
  cases t <;> simp_all [STL.Tree.IsDnf, STL.Tree.IsCube]

theorem STL.Tree.aux_dnfRewrite_zero (φ : STL.Tree n) :
    (φ.dnfRewrite).2 = 0 → (φ.dnfRewrite).1 = φ ∧ φ.IsDnf := by -- --- PROOF ---
  induction φ with
  | and φ ψ ihφ ihψ =>
    simp only [STL.Tree.dnfRewrite]
    split
    all_goals intro h
    all_goals first | omega | skip
    obtain ⟨a₁, a₂⟩ := ihφ (by omega)
    obtain ⟨b₁, b₂⟩ := ihψ (by omega)
    simp_all
    exact ⟨STL.Tree.aux_isCube_of_isDnf _ a₂ (by assumption),
      STL.Tree.aux_isCube_of_isDnf _ b₂ (by assumption)⟩
  | or φ ψ ihφ ihψ =>
    intro h
    obtain ⟨a₁, a₂⟩ := ihφ (by simp [STL.Tree.dnfRewrite] at h; omega)
    obtain ⟨b₁, b₂⟩ := ihψ (by simp [STL.Tree.dnfRewrite] at h; omega)
    simp [STL.Tree.dnfRewrite, STL.Tree.IsDnf, a₁, a₂, b₁, b₂]
  | _ => simp [STL.Tree.dnfRewrite, STL.Tree.IsDnf, STL.Tree.IsCube]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Tree.isDnf_dnfRewrite_of_snd_eq_zero (φ : STL.Tree n) (h : (φ.dnfRewrite).2 = 0) :
    (φ.dnfRewrite).1.IsDnf := by
  obtain ⟨h₁, h₂⟩ := STL.Tree.aux_dnfRewrite_zero φ h
  rwa [h₁]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
