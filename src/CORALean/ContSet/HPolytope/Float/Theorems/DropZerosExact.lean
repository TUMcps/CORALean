module

public import CORALean.ContSet.HPolytope.Float.Operations.DropZeros
public import CORALean.ContSet.HPolytope.Float.Theorems.IsZeroVecDot
public import CORALean.ContSet.HPolytope.Float.Theorems.MemRestrictIff
public import CORALean.ContSet.HPolytope.Float.Theorems.ConstructEmptySet

@[expose] public section

/-!
# `dropZeros` denotes the same set, exactly

A zero row `0 ≤ b` with `b ≥ 0` or `0 = be` holds at every point, so deleting it changes
nothing; a certified infeasible one empties the set, and the empty set is what is returned.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic

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
  · -- infeasible: the nominal part is empty, so both sets are
    have hN : Q.nominal.construct = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨h1, h2⟩ := HPolytope.mem_nominal_iff.mp hx
      -- the certified row is violated at every point
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨i, -, hz, hl⟩ | ⟨r, -, hz, hl⟩
      · have := toReal_lt_of_ltStrict hl
        have h3 := h1 i
        have hu := add_le_addUp (Q.b i) (absolute (Q.b_error i))
        rw [hzA i hz x] at h3
        rw [toReal_zero] at this
        rw [toReal_absolute] at hu
        linarith
      · have h3 := h2 r
        rw [hzE r hz x, zero_sub, abs_neg] at h3
        have := toReal_lt_of_ltStrict hl
        rw [toReal_absolute, toReal_absolute] at this
        linarith
    rw [HPolytope.construct_emptySet]
    show _ = Q.nominal.construct + Q.I_error.construct
    rw [hN, Set.empty_add]
  · -- no certified infeasible row: the deleted rows hold everywhere
    refine HPolytope.construct_congr ?_ rfl
    ext x
    -- membership in the restriction, against membership in `Q`
    rw [HPolytope.mem_restrict_iff, HPolytope.mem_nominal_iff]
    constructor
    · -- a dropped row is a certified zero row that holds
      rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun r => ?_⟩
      · by_cases hk : (!(HPolytope.isZeroVec (Q.A i) && le FloatOps.zero (Q.b i))) = true
        · exact h1 i hk
        · simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at hk
          rw [hzA i hk.1 x]
          have := toReal_le_of_le hk.2
          rw [toReal_zero] at this
          linarith [abs_nonneg (toReal (Q.b_error i))]
      · by_cases hk : (!(HPolytope.isZeroVec (Q.Ae r) && HPolytope.eqScalar (Q.be r) FloatOps.zero))
            = true
        · exact h2 r hk
        · simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at hk
          rw [hzE r hk.1 x, HPolytope.toReal_eq_of_eqScalar hk.2, toReal_zero, sub_zero, abs_zero]
          exact abs_nonneg _
    · rintro ⟨h1, h2⟩
      exact ⟨fun i _ => h1 i, fun r _ => h2 r⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
