module

public import CORALean.ContSet.HPolytope.Float.HPolytope

@[expose] public section

/-!
# A row with one nonzero entry reads one coordinate

The sign the entry carries times the coordinate; the other entries are `0` and drop out.

## Inputs
* `a` – scalar
* `x` – point of length `n`
* `j` – index below `n`

## Hypotheses
* none

## Conclusion
* A row with one nonzero entry reads one coordinate
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mulVec_single {a : 𝕋} (x : Vec ℝ n) (j : Fin n) : -- --- CONCL ---
    (toRealMat (fun j' k => if j' = k then a else zero) *ᵥ x) j
      = toReal a * x j := by -- --- PROOF ---
  show ∑ k, toReal (if j = k then a else zero) * x k = _
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl]
  · intro k _ hk
    rw [if_neg (Ne.symm hk), toReal_zero, zero_mul]
  · exact fun h => absurd (Finset.mem_univ j) h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
