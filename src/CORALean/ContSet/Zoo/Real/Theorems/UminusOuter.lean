module

public import CORALean.ContSet.Zoo.Real.Operations.Basic
public import CORALean.ContSet.Zoo.Real.Theorems.EnclosesIff
public import CORALean.ContSet.Taylm.Real.Theorems.UminusOuter
public import CORALean.ContSet.Interval.Real.Theorems.UminusExact

@[expose] public section

/-!
# `Zoo.uminus` encloses the negation

The Taylor model by `Taylm.uminus_outer`, the interval by `Interval.uminus_exact`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zoo.uminus_outer {Z : Zoo n} {f : Vec ℝ n → ℝ} (h : Z.Encloses f) :
    Z.uminus.Encloses fun t => -f t := by -- --- PROOF ---
  rw [Zoo.encloses_iff] at h ⊢
  refine ⟨fun T hT => ?_, fun I hI t ht => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hT
    exact Taylm.uminus_outer (h.1 a ha)
  · obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hI
    exact (Interval.uminus_exact a) ▸ Set.neg_mem_neg.2 (h.2 a ha t ht)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
