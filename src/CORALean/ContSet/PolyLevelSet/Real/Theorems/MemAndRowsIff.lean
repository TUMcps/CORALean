module

public import CORALean.ContSet.LevelSet.Real.Theorems.ForallAppendHolds
public import CORALean.ContSet.PolyLevelSet.Real.Operations.Basic
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalAnd

@[expose] public section

/-!
# A point of `PolyLevelSet.andRows`

A point of `P.andRows Q` is a point of `P`, its box included, at which `Q`'s rows hold as well:
`Q`'s box is not read. Where `Q`'s box contains `P`'s, this is `P.construct ∩ Q.construct`, as
`and_exact` states for `and_`.

## Inputs
* `P` – level set
* `Q` – level set whose rows are added
* `x` – point

## Hypotheses
* none

## Conclusion
* `x` lies in `P.andRows Q` iff it lies in `P` and meets `Q`'s rows
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of `P.andRows Q` is a point of `P` at which `Q`'s rows hold. -/
theorem PolyLevelSet.mem_andRows_iff (P Q : PolyLevelSet n) (x : Vec ℝ n) : -- --- CONCL ---
    x ∈ (P.andRows Q).construct
      ↔ x ∈ P.construct ∧ ∀ i, (Q.op i).holds (Q.eval x i) := by -- --- PROOF ---
  show (x ∈ P.dom.construct ∧ ∀ i, ((P.and_ Q).op i).holds ((P.and_ Q).eval x i)) ↔ _
  rw [PolyLevelSet.eval_and_]
  show (_ ∧ ∀ i, (Fin.append P.op Q.op i).holds _) ↔ _
  rw [LevelSet.forall_append_holds]
  exact ⟨fun ⟨h, r₁, r₂⟩ => ⟨⟨h, r₁⟩, r₂⟩, fun ⟨⟨h, r₁⟩, r₂⟩ => ⟨h, r₁, r₂⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
