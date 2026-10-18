module

public import CORALean.ContSet.ZonoBundle.Float.Operations.IntervalSupportFunc
public import CORALean.ContSet.ZonoBundle.Float.Theorems.IntervalAllContains
public import CORALean.ContSet.ZonoBundle.Float.Theorems.BoundDotLPLe
public import CORALean.ContSet.Interval.Float.Theorems.Basic

@[expose] public section

/-!
# `ZonoBundle.intervalSupportFunc` encloses the bundle, over a floating-point scalar

Every point of the bundle lies in CORA's box (`intervalAll_contains`) and reads at most each
certified support bound in its direction (`boundDotLP_le`), at `eᵢ` from above and at `-eᵢ` from
below; the minimum and the maximum of two sound ends are sound, both being exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The support-function box contains the bundle. -/
theorem ZonoBundle.intervalSupportFunc_outer (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k) :
    zB.construct ⊆ (zB.intervalSupportFunc hk).construct := by -- --- PROOF ---
  intro x hx
  refine Interval.mem_vec_iff.mpr fun i => ?_
  have hB := Interval.mem_vec_iff.mp (zB.intervalAll_contains hk hx) i
  -- the certified bounds in `eᵢ` and in `-eᵢ`
  have hu := zB.boundDotLP_le hk (c := LinearMap.proj i) (fun j => if j = i then one else zero)
    (fun x => by simp [apply_ite toReal, toReal_one, toReal_zero]) x hx
  have hd := zB.boundDotLP_le hk (c := -LinearMap.proj i)
    (fun j => if j = i then neg one else zero)
    (fun x => by simp [apply_ite toReal, toReal_neg, toReal_one, toReal_zero]) x hx
  simp only [LinearMap.proj_apply, LinearMap.neg_apply] at hu hd
  simp only [ZonoBundle.intervalSupportFunc, toReal_maximum, toReal_minimum, toReal_neg]
  exact ⟨max_le hB.1 (by linarith), le_min hB.2 hu⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
