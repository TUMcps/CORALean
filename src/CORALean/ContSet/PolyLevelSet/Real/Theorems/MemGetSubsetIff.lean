module

public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalGetSubset

@[expose] public section

/-!
# A point of `PolyLevelSet.getSubset`

`x` is in the re-parametrized set exactly when `x` with `xᵣ ↦ cen + rad xᵣ` is in the original.

## Inputs
* `P` – polynomial level set
* `r` – variable index
* `cen` – new center of the variable
* `rad` – new radius of the variable
* `x` – point

## Hypotheses
* none

## Conclusion
* `x` lies in the rescaled set iff the rescaled point lies in `P`
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `x` is in the re-parametrized set exactly when it is in `P`'s box and `P`'s rows hold at `x`
at `xᵣ ↦ cen + rad xᵣ`. -/
theorem PolyLevelSet.mem_getSubset_iff (P : PolyLevelSet n) (r : Fin n) (cen rad : ℝ)
    (x : Vec ℝ n) : x ∈ (P.getSubset r cen rad).construct
      ↔ x ∈ P.dom.construct
        ∧ ∀ i, (P.op i).holds (P.eval (Function.update x r (cen + rad * x r)) i) := by
  show (_ ∧ ∀ i, (P.op i).holds ((P.getSubset r cen rad).eval x i)) ↔ _
  rw [PolyLevelSet.eval_getSubset]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
