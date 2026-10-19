module

public import CORALean.ContSet.Interval.Float.Theorems.MemAppendIff
public import CORALean.ContSet.PolyLevelSet.Float.Theorems.EvalNominalCoreRelax

@[expose] public section

/-!
# What `PolyLevelSet.relax` denotes over a floating-point scalar

With every row an equation, the rows with their slacks moved into variables are the exact rows
relaxed by the slacks (`eval_nominalCore_relax`): the slack left is `zero`, so each row is met
exactly.

## Inputs
* `P` – polynomial level set
* `D` – box of the slack variables
* `x` – real point

## Hypotheses
* `h` – all rows are equations

## Conclusion
* `x` lies in the relaxed set iff it lies in the exact relaxation
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The slack-free relaxed rows denote the exact relaxation by the read-back slack. -/
theorem PolyLevelSet.mem_relax_iff {P : PolyLevelSet 𝕋 n} (h : ∀ i, P.op i = .eq)
    (D : Interval (Vec 𝕋 P.m)) (x : Vec ℝ (n + P.m)) :
    x ∈ (P.relax D).construct
      ↔ x ∈ (P.nominalCore.relax (toRealVec P.b_error) D.nominal).construct := by -- --- PROOF ---
  refine and_congr ?_ (forall_congr' fun i => ?_)
  -- the boxes: both are the appended read-back boxes
  · show x ∈ (P.dom.append D).construct ↔ x ∈ (P.dom.nominal.append D.nominal).construct
    rw [Interval.mem_append_iff, Real.Interval.mem_append_iff]
    rfl
  · show (P.op i).IsMetWithin ((P.relax D).nominalCore.eval x i) |toReal (zero : 𝕋)|
      ↔ (P.op i).holds ((P.nominalCore.relax (toRealVec P.b_error) D.nominal).eval x i)
    rw [PolyLevelSet.eval_nominalCore_relax, h i, toReal_zero, abs_zero]
    exact abs_nonpos_iff

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
