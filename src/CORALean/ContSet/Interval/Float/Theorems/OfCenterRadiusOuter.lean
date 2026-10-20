module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Real.Theorems.MemOfCenterRadius

@[expose] public section

/-!
# `Interval.ofCenterRadius` contains the exact box, over a floating-point scalar

The exact box of the stored center and radius read as reals: an entry within `r` of `c` lies
above `subDown c r ≤ c - r` and below `addUp c r ≥ c + r`.

## Inputs
* `c` – float center matrix
* `r` – float radius matrix

## Hypotheses
* none

## Conclusion
* the exact box built from center and radius lies in the float box
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.ofCenterRadius_outer (c r : Mat 𝕋 m n) : -- --- CONCL ---
    (Real.Interval.ofCenterRadius (toRealMat c) (toRealMat r)).construct
      ⊆ (Interval.ofCenterRadius c r).construct := by -- --- PROOF ---
  intro A hA
  refine Interval.mem_mat_iff.mpr fun i j => ?_
  have h : |A i j - toReal (c i j)| ≤ toReal (r i j) :=
    (Real.Interval.mem_ofCenterRadius _ _ A).mp hA (i, j)
  obtain ⟨h₁, h₂⟩ := abs_le.mp h
  exact ⟨le_trans (subDown_le_sub _ _) (by linarith),
    le_trans (by linarith) (add_le_addUp _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
