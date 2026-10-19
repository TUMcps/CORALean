module

public import CORALean.ContSet.Interval.Real.Theorems.MemAppendIff
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalCartProd
public import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds

@[expose] public section

/-!
# What `PolyLevelSet.cartProd` denotes

The product of the two sets, a point of it being one point of each side by side: the product's
values are the operands' at their own variables (`eval_cartProd`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the product is a point of each operand, box and rows, on its own block of
variables. -/
theorem PolyLevelSet.mem_cartProd_iff (P₁ : PolyLevelSet n₁) (P₂ : PolyLevelSet n₂)
    (x : Vec ℝ (n₁ + n₂)) : -- --- CONCL ---
    x ∈ (P₁.cartProd P₂).construct
      ↔ (fun k => x (Fin.castAdd n₂ k)) ∈ P₁.construct
        ∧ (fun k => x (Fin.natAdd n₁ k)) ∈ P₂.construct := by -- --- PROOF ---
  show (x ∈ (P₁.dom.append P₂.dom).construct
    ∧ ∀ i, ((P₁.cartProd P₂).op i).holds ((P₁.cartProd P₂).eval x i)) ↔ _
  rw [PolyLevelSet.eval_cartProd, Interval.mem_append_iff]
  show (_ ∧ ∀ i, (Fin.append P₁.op P₂.op i).holds _) ↔ _
  rw [LevelSet.forall_append_holds]
  exact ⟨fun ⟨⟨h₁, h₂⟩, r₁, r₂⟩ => ⟨⟨h₁, r₁⟩, h₂, r₂⟩, fun ⟨⟨h₁, r₁⟩, h₂, r₂⟩ => ⟨⟨h₁, h₂⟩, r₁, r₂⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
