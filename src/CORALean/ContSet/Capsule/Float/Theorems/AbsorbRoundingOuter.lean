module

public import CORALean.ContSet.Capsule.Float.Theorems.Norm2LeErrorNorm
public import CORALean.ContSet.Capsule.Float.Operations.AbsorbRounding
public import CORALean.ContSet.Capsule.Float.Theorems.Basic
public import CORALean.ContSet.Capsule.Float.Theorems.MemConstructOfSplit
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact

@[expose] public section

/-!
# `Capsule.absorbRounding` loses no point

A point is `c + t g + w + e` with `‖w‖₂ ≤ r` and `e` in the box, so `‖e‖₂ ≤ errorNorm`
(`norm₂_le_errorNorm`), and `w + e` is no longer than the raised radius by the triangle inequality.
Nothing is left over, and the result's box, the origin, holds it.

## Inputs
* `k` – Newton steps for sqrt
* `C` – capsule with error box

## Hypotheses
* none

## Conclusion
* the capsule is contained in its absorbed version
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open CORALean Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `absorbRounding` contains the set. -/
theorem Capsule.absorbRounding_outer (k : ℕ) (C : Capsule 𝕋 n) :
    C.construct ⊆ (C.absorbRounding k).construct := by -- --- PROOF ---
  rintro _ ⟨y, hy, e, he, rfl⟩
  obtain ⟨t, ht, w, hw, rfl⟩ := Capsule.exists_split_of_mem hy
  refine Capsule.mem_construct_of_split _ ht (w := w + e) ?_ ?_
  · -- the two lengths, under the radius raised by the box's bound
    have h₁ := Capsule.norm₂_le_errorNorm k C he
    have h₂ := add_le_addUp C.r (C.errorNorm k)
    have h₃ := norm₂_add_le w e
    have hw' : ‖w‖₂ ≤ toReal C.r := hw
    show _ ≤ toReal (addUp C.r (C.errorNorm k))
    linarith
  · -- nothing is left, and the origin is in the box
    show _ ∈ (Interval.origin n : Interval (Vec 𝕋 n)).construct
    rw [Interval.origin_exact, Set.mem_singleton_iff]
    show toRealVec C.c + t • toRealVec C.g + w + e - (toRealVec C.c + t • toRealVec C.g + (w + e))
      = 0
    abel

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
