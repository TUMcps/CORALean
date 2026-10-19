module

public import CORALean.ContSet.Interval.Real.Theorems.MemAppendIff
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalPadVars

@[expose] public section

/-!
# What `PolyLevelSet.padVars` denotes

The set times the whole space of the fresh variables: no row reads them (`eval_padVars`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point is in the padded set exactly when its first `n` variables are in the set and its
last `r` in the new box. -/
theorem PolyLevelSet.mem_padVars_iff (P : PolyLevelSet n) {r : ℕ} (D : Interval (Vec ℝ r))
    (x : Vec ℝ (n + r)) : -- --- STMT ---
    x ∈ (P.padVars D).construct
      ↔ (fun k => x (Fin.castAdd r k)) ∈ P.construct
        ∧ (fun k => x (Fin.natAdd n k)) ∈ D.construct := by -- --- PROOF ---
  show (x ∈ (P.dom.append D).construct ∧ ∀ i, (P.op i).holds ((P.padVars D).eval x i)) ↔ _
  rw [PolyLevelSet.eval_padVars, Interval.mem_append_iff]
  exact ⟨fun ⟨⟨h₁, h₂⟩, r₁⟩ => ⟨⟨h₁, r₁⟩, h₂⟩, fun ⟨⟨h₁, r₁⟩, h₂⟩ => ⟨⟨h₁, h₂⟩, r₁⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
