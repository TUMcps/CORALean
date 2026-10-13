module

public import CORALean.ContSet.HPolytope.Float.Operations.IsInvertedPair
public import CORALean.ContSet.HPolytope.Float.Theorems.EqVecEq

@[expose] public section

/-!
# An inverted pair of rows has opposite values

At every point, row `j` takes the negative of row `i`'s value, and its right-hand side is the
negative of `i`'s.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isInvertedPair_dot {Q : HPolytope 𝕋 (Vec 𝕋 n)} {i j : Fin Q.m}
    (h : HPolytope.isInvertedPair Q i j = true) (x : Vec ℝ n) :
    (toRealMat Q.A *ᵥ x) j = -(toRealMat Q.A *ᵥ x) i ∧
      toReal (Q.b j) = -toReal (Q.b i) := by -- --- PROOF ---
  simp only [HPolytope.isInvertedPair, Bool.and_eq_true] at h
  refine ⟨?_, (HPolytope.toReal_eq_of_eqScalar h.1.1.2).trans (toReal_neg _)⟩
  simp only [mulVec, dotProduct, toRealMat, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [HPolytope.toReal_eq_of_eqVec h.1.1.1 c, toReal_neg, neg_mul]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
