module

public import CORALean.ContSet.StarSet.Float.Operations.Basic
public import CORALean.ContSet.StarSet.Float.StarSet

@[expose] public section

/-!
# What `StarSet.LinPred.append` admits

Factors `(α, e)` meet the extended predicate exactly when `α` meets the old one and each `e k`
lies in its new range: every old row reads the new factors through its padded zeros as nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The old factors meet the old predicate and the new ones lie in their ranges. -/
theorem StarSet.LinPred.mem_append_nominal_iff (p : StarSet.LinPred 𝕋 m) (lo hi : Fin k → 𝕋)
    (α : Vec ℝ m) (e : Vec ℝ k) : -- --- STMT ---
    (Fin.append α e : Vec ℝ (m + k)) ∈ ContSet.construct (p.append lo hi).nominal
      ↔ α ∈ ContSet.construct p.nominal
        ∧ ∀ j, toReal (lo j) ≤ e j ∧ e j ≤ toReal (hi j) := by -- --- PROOF ---
  simp only [ContSet.construct, CORALean.Real.StarSet.LinPred.construct, StarSet.LinPred.append,
    Set.mem_setOf_eq, List.map_map, List.forall_mem_map,
    Function.comp_def, Fin.forall_fin_add, Fin.append_left, Fin.append_right, Fin.sum_univ_add,
    toReal_zero, zero_mul, Finset.sum_const_zero, add_zero]
  tauto

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
