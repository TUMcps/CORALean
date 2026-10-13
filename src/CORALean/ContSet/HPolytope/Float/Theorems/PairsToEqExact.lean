import CORALean.ContSet.HPolytope.Float.Operations.PairsToEq
import CORALean.ContSet.HPolytope.Float.Theorems.IsInvertedPairDot
import CORALean.ContSet.HPolytope.Float.Theorems.IsInvertedPairSymm
import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

/-!
# `pairsToEq` denotes the same set, exactly

A pair `aᵀx ≤ b`, `-aᵀx ≤ -b` is the equality `aᵀx = b`, and the equalities appended imply the
rows moved: a moved row is the lead of its pair or the negation of it.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.pairsToEq_exact (Q : HPolytope 𝕋 (Vec 𝕋 n)) :
    Q.pairsToEq.construct = Q.construct := by -- --- PROOF ---
  ext x
  rw [HPolytope.mem_construct_iff, HPolytope.mem_construct_iff]
  -- the rows of the result, read in `Q`
  have hkA : ∀ k, (toRealMat Q.pairsToEq.A *ᵥ x) k = (toRealMat Q.A *ᵥ x) (Q.keptRows.get k) :=
    fun k => rfl
  -- the old equality rows and the appended ones
  have hold : ∀ r, (toRealMat Q.pairsToEq.Ae *ᵥ x) (Fin.castAdd _ r) = (toRealMat Q.Ae *ᵥ x) r := by
    intro r
    simp [mulVec, dotProduct, toRealMat, HPolytope.pairsToEq, Fin.append_left]
  have hnew : ∀ k, (toRealMat Q.pairsToEq.Ae *ᵥ x) (Fin.natAdd Q.me k)
      = (toRealMat Q.A *ᵥ x) (Q.leadRows.get k) := by
    intro k
    simp [mulVec, dotProduct, toRealMat, HPolytope.pairsToEq, Fin.append_right]
  have hbinf : ∀ k, toReal (Q.pairsToEq.be.inf (Fin.natAdd Q.me k))
      = toReal (Q.b (Q.leadRows.get k)) := by
    intro k
    simp [HPolytope.pairsToEq, Fin.append_right]
  have hbsup : ∀ k, toReal (Q.pairsToEq.be.sup (Fin.natAdd Q.me k))
      = toReal (Q.b (Q.leadRows.get k)) := by
    intro k
    simp [HPolytope.pairsToEq, Fin.append_right]
  have hbold : ∀ r, Q.pairsToEq.be.inf (Fin.castAdd _ r) = Q.be.inf r
      ∧ Q.pairsToEq.be.sup (Fin.castAdd _ r) = Q.be.sup r := by
    intro r
    simp [HPolytope.pairsToEq, Fin.append_left]
  -- every row with a partner is, or is the negation of, a row listed as a lead
  have hlead : ∀ i j, HPolytope.isInvertedPair Q i j = true → ∃ k,
      (Q.leadRows.get k = i ∧ HPolytope.isInvertedPair Q i j = true) ∨
        (Q.leadRows.get k = j ∧ HPolytope.isInvertedPair Q j i = true) := by
    intro i j h
    by_cases hij : i ≤ j
    · obtain ⟨k, hk⟩ := List.mem_iff_get.mp (List.mem_filter.mpr ⟨List.mem_finRange i,
        List.any_eq_true.mpr ⟨j, List.mem_finRange j, by simp [h, hij]⟩⟩ :
        i ∈ Q.leadRows)
      exact ⟨k, Or.inl ⟨hk, h⟩⟩
    · have hs := HPolytope.isInvertedPair_symm h
      obtain ⟨k, hk⟩ := List.mem_iff_get.mp (List.mem_filter.mpr ⟨List.mem_finRange j,
        List.any_eq_true.mpr ⟨i, List.mem_finRange i, by simp [hs, (not_le.mp hij).le]⟩⟩ :
        j ∈ Q.leadRows)
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
        obtain ⟨k, hk | hk⟩ := hlead i j hj
        · have e1 := (h2 (Fin.natAdd Q.me k)).2
          rw [hnew, hbsup, hk.1] at e1
          exact e1
        · have e1 := (h2 (Fin.natAdd Q.me k)).1
          rw [hnew, hbinf, hk.1] at e1
          obtain ⟨d1, d2⟩ := HPolytope.isInvertedPair_dot hj x
          linarith
      · have hmem : i ∈ Q.keptRows := List.mem_filter.mpr ⟨List.mem_finRange i, by simpa using hm⟩
        obtain ⟨k, hk⟩ := List.mem_iff_get.mp hmem
        have := h1 k
        have hb : Q.pairsToEq.b k = Q.b i := by
          show Q.b (Q.keptRows.get k) = _
          rw [hk]
        rw [hkA, hk, hb] at this
        exact this
    · have := h2 (Fin.castAdd _ r)
      rw [hold, (hbold r).1, (hbold r).2] at this
      exact this
  · -- `Q` implies the result: a listed pair is squeezed to an equality
    rintro ⟨h1, h2⟩
    refine ⟨fun k => ?_, fun r => ?_⟩
    · rw [hkA]
      exact h1 _
    · refine Fin.addCases (fun r => ?_) (fun k => ?_) r
      · rw [hold, (hbold r).1, (hbold r).2]
        exact h2 r
      · -- the lead row has a partner, whose value is its negative
        have hmem := List.get_mem Q.leadRows k
        obtain ⟨-, hl⟩ := List.mem_filter.mp hmem
        obtain ⟨j, -, hj⟩ := List.any_eq_true.mp hl
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
        obtain ⟨d1, d2⟩ := HPolytope.isInvertedPair_dot hj.1 x
        have e1 := h1 (Q.leadRows.get k)
        have e2 := h1 j
        rw [hnew, hbinf, hbsup]
        constructor <;> linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
