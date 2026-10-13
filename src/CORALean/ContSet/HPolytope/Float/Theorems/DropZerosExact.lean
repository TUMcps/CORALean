import CORALean.ContSet.HPolytope.Float.Operations.DropZeros
import CORALean.ContSet.HPolytope.Float.Theorems.IsZeroVecDot
import CORALean.ContSet.HPolytope.Float.Theorems.MemRestrictIff
import CORALean.ContSet.HPolytope.Float.Theorems.ConstructEmptySet

/-!
# `dropZeros` denotes the same set, exactly

A zero row `0 ≤ b` with `b ≥ 0` or `0 ∈ [lo, hi]` holds at every point, so deleting it changes
nothing; a certified infeasible one empties the set, and the empty set is what is returned.
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

theorem HPolytope.dropZeros_exact (Q : HPolytope 𝕋 (Vec 𝕋 n)) :
    Q.dropZeros.construct = Q.construct := by -- --- PROOF ---
  unfold HPolytope.dropZeros
  -- a certified zero row has the value `0` at every point
  have hzA : ∀ i, HPolytope.isZeroVec (Q.A i) = true → ∀ x : Vec ℝ n,
      (toRealMat Q.A *ᵥ x) i = 0 := fun i h x => HPolytope.isZeroVec_dot h x
  have hzE : ∀ r, HPolytope.isZeroVec (Q.Ae r) = true → ∀ x : Vec ℝ n,
      (toRealMat Q.Ae *ᵥ x) r = 0 := fun r h x => HPolytope.isZeroVec_dot h x
  split_ifs with h
  · -- infeasible: both sets are empty
    rw [HPolytope.construct_emptySet]
    refine (Set.eq_empty_of_forall_notMem fun x hx => ?_).symm
    obtain ⟨h1, h2⟩ := HPolytope.mem_construct_iff.mp hx
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨i, -, hz, hl⟩ | ⟨r, -, hz, hl⟩
    · have := toReal_lt_of_ltStrict hl
      have h3 := h1 i
      rw [hzA i hz x] at h3
      rw [toReal_zero] at this
      linarith
    · have h3 := h2 r
      rw [hzE r hz x] at h3
      rcases hl with hl | hl
      · have := toReal_lt_of_ltStrict hl
        rw [toReal_zero] at this
        linarith [h3.1]
      · have := toReal_lt_of_ltStrict hl
        rw [toReal_zero] at this
        linarith [h3.2]
  · -- no certified infeasible row: the deleted rows hold everywhere
    ext x
    -- membership in the restriction, against membership in `Q`
    rw [HPolytope.mem_restrict_iff, HPolytope.mem_construct_iff]
    constructor
    · -- a dropped row is a certified zero row that holds
      rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun r => ?_⟩
      · by_cases hk : (!(HPolytope.isZeroVec (Q.A i) && le FloatOps.zero (Q.b i))) = true
        · exact h1 i hk
        · simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at hk
          rw [hzA i hk.1 x]
          have := toReal_le_of_le hk.2
          rwa [toReal_zero] at this
      · by_cases hk : (!(HPolytope.isZeroVec (Q.Ae r) && le (Q.be.inf r) FloatOps.zero &&
            le FloatOps.zero (Q.be.sup r))) = true
        · exact h2 r hk
        · simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at hk
          rw [hzE r hk.1.1 x]
          have h3 := toReal_le_of_le hk.1.2
          have h4 := toReal_le_of_le hk.2
          rw [toReal_zero] at h3 h4
          exact ⟨h3, h4⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun i _ => h1 i, fun r _ => h2 r⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
