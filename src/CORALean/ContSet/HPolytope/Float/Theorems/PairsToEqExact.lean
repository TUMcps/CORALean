module

public import CORALean.ContSet.HPolytope.Float.Operations.PairsToEq
public import CORALean.ContSet.HPolytope.Float.Theorems.IsInvertedPairDot
public import CORALean.ContSet.HPolytope.Float.Theorems.IsInvertedPairSymm
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# `pairsToEq` denotes the same set, exactly

A pair `aᵀx ≤ b`, `-aᵀx ≤ -b` is the equality `aᵀx = b`, and the equalities appended imply the
rows moved: a moved row is the lead of its pair or the negation of it.

## Inputs
* `Q` – H-polytope

## Hypotheses
* none

## Conclusion
* `pairsToEq` denotes the same set, exactly
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

theorem HPolytope.pairsToEq_exact (Q : HPolytope 𝕋 (Vec 𝕋 n)) :
    Q.pairsToEq.construct = Q.construct := by -- --- PROOF ---
  refine HPolytope.construct_congr ?_ rfl
  ext x
  rw [HPolytope.mem_nominal_iff, HPolytope.mem_nominal_iff]
  -- the rows of the result, read in `Q`
  have hkA : ∀ k, (toRealMat Q.pairsToEq.A *ᵥ x) k = (toRealMat Q.A *ᵥ x) (Q.aux_keptRows.get k) :=
    fun k => rfl
  -- the old equality rows and the appended ones
  have hold : ∀ r, (toRealMat Q.pairsToEq.Ae *ᵥ x) (Fin.castAdd _ r) = (toRealMat Q.Ae *ᵥ x) r := by
    intro r
    simp [mulVec, dotProduct, toRealMat, HPolytope.pairsToEq, Fin.append_left]
  have hnew : ∀ k, (toRealMat Q.pairsToEq.Ae *ᵥ x) (Fin.natAdd Q.me k)
      = (toRealMat Q.A *ᵥ x) (Q.aux_leadRows.get k) := by
    intro k
    simp [mulVec, dotProduct, toRealMat, HPolytope.pairsToEq, Fin.append_right]
  have hbnew : ∀ k, toReal (Q.pairsToEq.be (Fin.natAdd Q.me k))
      = toReal (Q.b (Q.aux_leadRows.get k)) := by
    intro k
    simp [HPolytope.pairsToEq, Fin.append_right]
  have hbold : ∀ r, Q.pairsToEq.be (Fin.castAdd _ r) = Q.be r := by
    intro r
    simp [HPolytope.pairsToEq, Fin.append_left]
  -- the slacks: carried on the kept and the old rows, `zero` on the appended equalities
  have hkE : ∀ k, Q.pairsToEq.b_error k = Q.b_error (Q.aux_keptRows.get k) := fun k => rfl
  have hee : ∀ r, Q.pairsToEq.be_error (Fin.castAdd _ r) = Q.be_error r := by
    intro r
    simp [HPolytope.pairsToEq, Fin.append_left]
  have hee' : ∀ k, toReal (Q.pairsToEq.be_error (Fin.natAdd Q.me k)) = 0 := by
    intro k
    simp [HPolytope.pairsToEq, Fin.append_right, toReal_zero]
  -- an inverted pair carries no slack, certified
  have hz : ∀ {i j}, HPolytope.isInvertedPair Q i j = true →
      toReal (Q.b_error i) = 0 ∧ toReal (Q.b_error j) = 0 := by
    intro i j h
    simp only [HPolytope.isInvertedPair, Bool.and_eq_true] at h
    exact ⟨(HPolytope.toReal_eq_of_eqScalar h.2.1).trans toReal_zero,
      (HPolytope.toReal_eq_of_eqScalar h.2.2).trans toReal_zero⟩
  -- every row with a partner is, or is the negation of, a row listed as a lead
  have hlead : ∀ i j, HPolytope.isInvertedPair Q i j = true → ∃ k,
      (Q.aux_leadRows.get k = i ∧ HPolytope.isInvertedPair Q i j = true) ∨
        (Q.aux_leadRows.get k = j ∧ HPolytope.isInvertedPair Q j i = true) := by
    intro i j h
    by_cases hij : i ≤ j
    · obtain ⟨k, hk⟩ := List.mem_iff_get.mp (List.mem_filter.mpr ⟨List.mem_finRange i,
        List.any_eq_true.mpr ⟨j, List.mem_finRange j, by simp [h, hij]⟩⟩ :
        i ∈ Q.aux_leadRows)
      exact ⟨k, Or.inl ⟨hk, h⟩⟩
    · have hs := HPolytope.isInvertedPair_symm h
      obtain ⟨k, hk⟩ := List.mem_iff_get.mp (List.mem_filter.mpr ⟨List.mem_finRange j,
        List.any_eq_true.mpr ⟨i, List.mem_finRange i, by simp [hs, (not_le.mp hij).le]⟩⟩ :
        j ∈ Q.aux_leadRows)
      exact ⟨k, Or.inr ⟨hk, hs⟩⟩
  -- the two directions
  constructor
  · -- the result implies `Q`: a moved row is a listed equality or its negation
    rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun r => ?_⟩
    · -- a row with a partner is a lead or the negation of one
      by_cases hm : ((List.finRange Q.m).any fun j => HPolytope.isInvertedPair Q i j) = true
      · -- the lead's equality gives both bounds
        obtain ⟨j, -, hj⟩ := List.any_eq_true.mp hm
        have hab := abs_nonneg (toReal (Q.b_error i))
        obtain ⟨k, hk | hk⟩ := hlead i j hj
        · have e1 := h2 (Fin.natAdd Q.me k)
          rw [hnew, hbnew, hee' k, abs_zero, abs_nonpos_iff, sub_eq_zero, hk.1] at e1
          linarith
        · have e1 := h2 (Fin.natAdd Q.me k)
          rw [hnew, hbnew, hee' k, abs_zero, abs_nonpos_iff, sub_eq_zero, hk.1] at e1
          obtain ⟨d1, d2⟩ := HPolytope.isInvertedPair_dot hj x
          linarith
      · -- a row without a partner is kept, its slack with it
        have hmem : i ∈ Q.aux_keptRows :=
          List.mem_filter.mpr ⟨List.mem_finRange i, by simpa using hm⟩
        obtain ⟨k, hk⟩ := List.mem_iff_get.mp hmem
        have := h1 k
        have hb : Q.pairsToEq.b k = Q.b i := by
          show Q.b (Q.aux_keptRows.get k) = _
          rw [hk]
        rw [hkA, hk, hb, hkE, hk] at this
        exact this
    · have := h2 (Fin.castAdd _ r)
      rw [hold, hbold r, hee r] at this
      exact this
  · -- `Q` implies the result: a listed pair is squeezed to an equality
    rintro ⟨h1, h2⟩
    refine ⟨fun k => ?_, fun r => ?_⟩
    · rw [hkA, hkE]
      exact h1 _
    · refine Fin.addCases (fun r => ?_) (fun k => ?_) r
      · rw [hold, hbold r, hee r]
        exact h2 r
      · -- the lead row has a partner, whose value is its negative
        have hmem := List.get_mem Q.aux_leadRows k
        obtain ⟨-, hl⟩ := List.mem_filter.mp hmem
        obtain ⟨j, -, hj⟩ := List.any_eq_true.mp hl
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
        obtain ⟨d1, d2⟩ := HPolytope.isInvertedPair_dot hj.1 x
        obtain ⟨hzl, hzj⟩ := hz hj.1
        have e1 := h1 (Q.aux_leadRows.get k)
        have e2 := h1 j
        rw [hzl, abs_zero, add_zero] at e1
        rw [hzj, abs_zero, add_zero] at e2
        rw [hnew, hbnew, hee' k, abs_zero, abs_nonpos_iff, sub_eq_zero]
        exact le_antisymm e1 (by linarith)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
