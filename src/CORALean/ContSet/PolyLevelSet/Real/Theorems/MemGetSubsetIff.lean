module

public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalGetSubset

@[expose] public section

/-!
# A point of `PolyLevelSet.getSubset`

`x` is in the re-parametrized set exactly when `x` with `xᵣ ↦ cen + rad xᵣ` is in the original.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x` is in the re-parametrized set exactly when `x` at `xᵣ ↦ cen + rad xᵣ` is in `P`. -/
theorem PolyLevelSet.mem_getSubset_iff (P : PolyLevelSet n) (r : Fin n) (cen rad : ℝ)
    (x : Vec ℝ n) :
    x ∈ (P.getSubset r cen rad).construct
      ↔ Function.update x r (cen + rad * x r) ∈ P.construct := by
  show (∀ i, (P.op i).holds ((P.getSubset r cen rad).eval x i)) ↔ _
  rw [PolyLevelSet.eval_getSubset]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
