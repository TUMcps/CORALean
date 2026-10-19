module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.MemAppendIff
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# A point of an appended box, over a floating-point scalar

The bounds are copied, so the stored box appended reads back as the exact boxes appended, and a
point lies in it iff each block lies in its own box (`Real.Interval.mem_append_iff`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the appended stored box is one whose two blocks lie in the two boxes. -/
theorem Interval.mem_append_iff (I₁ : Interval (Vec 𝕋 n₁)) (I₂ : Interval (Vec 𝕋 n₂))
    (x : Vec ℝ (n₁ + n₂)) : -- --- CONCL ---
    x ∈ (I₁.append I₂).construct
      ↔ (fun k => x (Fin.castAdd n₂ k)) ∈ I₁.construct
        ∧ (fun k => x (Fin.natAdd n₁ k)) ∈ I₂.construct := by -- --- PROOF ---
  -- the appended stored bounds read back as the appended exact ones
  show x ∈ (I₁.append I₂).nominal.construct ↔ _
  rw [Interval.nominal_append]
  exact Real.Interval.mem_append_iff _ _ x

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
