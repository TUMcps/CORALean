module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic

@[expose] public section

/-!
# `HPolytope.isErrFree` proves the polytope error-free

Each bound was certified equal to `zero` by `le` both ways, and `le` is sound.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.errFree_of_isErrFree {P : HPolytope 𝕋 (Vec 𝕋 n)} (h : P.isErrFree = true) :
    P.ErrFree := by -- --- PROOF ---
  simp only [HPolytope.isErrFree, Bool.and_eq_true] at h
  have hz : ∀ {k : ℕ} {v : Vec 𝕋 k}, HPolytope.isZeroVec v = true → ∀ j, toReal (v j) = 0 :=
    fun hv j => (HPolytope.toReal_eq_of_eqScalar
      (List.all_eq_true.mp hv j (List.mem_finRange j))).trans toReal_zero
  -- the box, the inequality slack, the equality slack
  exact ⟨fun j => ⟨hz h.1.1 j, hz h.1.2 j⟩, fun i => hz h.2.1 i, fun i => hz h.2.2 i⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
