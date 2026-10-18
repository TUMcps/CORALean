module

public import CORALean.ContSet.Capsule.Float.Operations.Basic
public import CORALean.ContSet.Capsule.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact
public import CORALean.ContSet.Capsule.Real.Theorems.OfPointMemIff
public import CORALean.ContSet.Capsule.Float.Theorems.ConstructEqNominal

@[expose] public section

/-!
# `Capsule.origin` is exactly the origin

`zero` reads as `0`, so the stored capsule is the exact layer's point capsule at the origin.
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

theorem Capsule.origin_exact (n : ℕ) :
    (Capsule.origin n : Capsule 𝕋 n).construct = {0} := by -- --- PROOF ---
  have h : (Capsule.origin n : Capsule 𝕋 n).nominal = Real.Capsule.ofPoint (0 : Vec ℝ n) := by
    unfold Capsule.nominal Capsule.origin Real.Capsule.ofPoint
    congr 1
    · funext i; exact toReal_zero
    · funext i; exact toReal_zero
    · exact toReal_zero
  rw [Capsule.construct_eq_nominal (Interval.origin_exact n)]
  show (Capsule.origin n : Capsule 𝕋 n).nominal.construct = {0}
  rw [h]
  exact Set.ext fun x =>
    (Real.Capsule.mem_ofPoint_iff (0 : Vec ℝ n) x).trans Set.mem_singleton_iff.symm

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
