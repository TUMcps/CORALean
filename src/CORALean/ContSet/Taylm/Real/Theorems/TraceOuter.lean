module

public import CORALean.ContSet.Taylm.Real.Operations.Trace
public import CORALean.ContSet.Taylm.Real.Theorems.SumOuter

@[expose] public section

/-!
# `Taylm.trace` encloses the trace
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.trace_outer {k : ℕ} {A : Fin k → Fin k → Taylm n}
    {f : Fin k → Fin k → Vec ℝ n → ℝ} (h : ∀ i j, (A i j).Encloses (f i j)) :
    (Taylm.trace A).Encloses fun t => ∑ i, f i i t :=
  Taylm.sum_outer fun i => h i i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
