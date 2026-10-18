module

public import CORALean.ContSet.Capsule.Float.Operations.Basic
public import CORALean.ContSet.Capsule.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact
public import CORALean.ContSet.Capsule.Real.Theorems.Basic
public import CORALean.ContSet.Capsule.Float.Theorems.ConstructEqNominal

@[expose] public section

/-!
# `Capsule.empty` is exactly empty

`neg one` reads as `-1`, so the stored capsule is the exact layer's empty one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Capsule.empty_exact (n : ℕ) :
    (Capsule.empty n : Capsule 𝕋 n).construct = ∅ := by -- --- PROOF ---
  have h : (Capsule.empty n : Capsule 𝕋 n).nominal = Real.Capsule.empty n := by
    unfold Capsule.nominal Capsule.empty Real.Capsule.empty
    congr 1
    · funext i; exact toReal_zero
    · funext i; exact toReal_zero
    · rw [toReal_neg, toReal_one]
  rw [Capsule.construct_eq_nominal (Interval.origin_exact n)]
  show (Capsule.empty n : Capsule 𝕋 n).nominal.construct = ∅
  rw [h]
  exact Real.Capsule.empty_exact n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
