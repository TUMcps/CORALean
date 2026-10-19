module

public import CORALean.ContSet.Interval.Float.Theorems.MemAppendIff
public import CORALean.ContSet.PolyLevelSet.Float.Operations.PadVars
public import CORALean.ContSet.PolyLevelSet.Real.Theorems.EvalPadVars

@[expose] public section

/-!
# What `PolyLevelSet.padVars` denotes over a floating-point scalar

The set times the whole space of the fresh variables: the padded rows read back as the exact
padded rows, which ignore them (`Real.PolyLevelSet.eval_padVars`).

## Inputs
* `P` – polynomial level set
* `r` – number of fresh variables
* `D` – box of the fresh variables
* `x` – real point

## Hypotheses
* none

## Conclusion
* `x` lies in the padded set iff its two parts lie in `P` and `D`
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

/-- A point is in the padded set exactly when its first `n` variables are in the set and its
last `r` in the new box. -/
theorem PolyLevelSet.mem_padVars_iff (P : PolyLevelSet 𝕋 n) {r : ℕ} (D : Interval (Vec 𝕋 r))
    (x : Vec ℝ (n + r)) : -- --- CONCL ---
    x ∈ (P.padVars D).construct
      ↔ (fun k => x (Fin.castAdd r k)) ∈ P.construct
        ∧ (fun k => x (Fin.natAdd n k)) ∈ D.construct := by -- --- PROOF ---
  show (x ∈ (P.dom.append D).construct
    ∧ ∀ i, (P.op i).IsMetWithin (P.nominalCore.padVars D.nominal |>.eval x i) _) ↔ _
  rw [Real.PolyLevelSet.eval_padVars, Interval.mem_append_iff]
  exact ⟨fun ⟨⟨h₁, h₂⟩, r₁⟩ => ⟨⟨h₁, r₁⟩, h₂⟩, fun ⟨⟨h₁, r₁⟩, h₂⟩ => ⟨⟨h₁, h₂⟩, r₁⟩⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
