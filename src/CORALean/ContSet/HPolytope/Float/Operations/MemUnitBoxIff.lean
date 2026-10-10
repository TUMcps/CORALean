import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLeft
import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendRight
import CORALean.ContSet.HPolytope.Float.Operations.MulVecSingle
import CORALean.ContSet.HPolytope.Float.Operations.UnitBox

/-!
# Membership in `HPolytope.unitBox`, over a floating-point scalar

The two constraint halves read back as a bound on the magnitude, as over ℝ. A
row is one coordinate: the sum collapses at the single entry that is not zero.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- membership is those two halves read back as a bound on the magnitude
theorem HPolytope.mem_unitBox_iff {x : Vec ℝ n} :
    x ∈ (HPolytope.unitBox 𝕋 n).construct ↔ ∀ j, |x j| ≤ 1 := by -- --- PROOF ---
  constructor
  · intro hmem j
    obtain ⟨hle, -⟩ := HPolytope.mem_construct_iff.mp hmem
    have hup := hle (Fin.castAdd n j)
    have hlo := hle (Fin.natAdd n j)
    simp only [HPolytope.unitBox, HPolytope.mulVec_append_left, HPolytope.mulVec_append_right,
      HPolytope.mulVec_single, toReal_one, toReal_neg, one_mul, neg_mul] at hup hlo
    exact abs_le.mpr ⟨by linarith, hup⟩
  -- back, the lower half being the negated coordinate
  · intro h
    refine HPolytope.mem_construct_iff.mpr ⟨?_, fun i => i.elim0⟩
    refine Fin.addCases (fun j => ?_) fun j => ?_
    · simp only [HPolytope.unitBox, HPolytope.mulVec_append_left, HPolytope.mulVec_single,
        toReal_one, one_mul]
      exact (abs_le.mp (h j)).2
    · simp only [HPolytope.unitBox, HPolytope.mulVec_append_right, HPolytope.mulVec_single,
        toReal_one, toReal_neg, neg_mul, one_mul]
      have := (abs_le.mp (h j)).1
      linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
