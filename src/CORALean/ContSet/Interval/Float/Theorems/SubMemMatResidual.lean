module

public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# What is left over after storing a rounded matrix

`Interval.sub_mem_residual` at `Mat 𝕋 m n`, the pair index taken apart the way
`Interval.mem_mat_iff` does.

## Inputs
* `lo` – float lower bound matrix
* `hi` – float upper bound matrix
* `stored` – stored float matrix
* `A` – real matrix

## Hypotheses
* `h` – `A` lies between the bounds

## Conclusion
* the residual of `A` against the stored matrix lies in the residual box
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.sub_mem_matResidual {lo hi stored : Mat 𝕋 m n} {A : Mat ℝ m n}
    (h : ∀ i j, toReal (lo i j) ≤ A i j ∧ A i j ≤ toReal (hi i j)) :
    (fun i j => A i j - toReal (stored i j)) ∈ (Interval.matResidual lo hi stored).construct :=
  fun p =>
    ⟨le_trans (subDown_le_sub _ _) (sub_le_sub_right (h p.1 p.2).1 _),
     le_trans (sub_le_sub_right (h p.1 p.2).2 _) (sub_le_subUp _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
