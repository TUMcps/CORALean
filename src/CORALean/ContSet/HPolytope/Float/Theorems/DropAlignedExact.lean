import CORALean.ContSet.HPolytope.Float.Operations.DropAligned
import CORALean.ContSet.HPolytope.Float.Theorems.EqVecEq
import CORALean.ContSet.HPolytope.Float.Theorems.MemRestrictIff

/-!
# `dropAligned` denotes the same set, exactly

A deleted row is dominated by a row with the same normal and a right-hand side at most its own.
That row may itself be deleted, but the dominating rows come down in the lexicographic order of
`(b, index)`, so among the finitely many rows with that normal and `b` at most the deleted row's,
the least is kept, and it implies the deleted row.
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

theorem HPolytope.dropAligned_exact (Q : HPolytope 𝕋 (Vec 𝕋 n)) :
    Q.dropAligned.construct = Q.construct := by -- --- PROOF ---
  -- every row is implied by a kept row with its normal and a right-hand side at most its own
  have key : ∀ i, ∃ k, (!(List.finRange Q.m).any fun j =>
        HPolytope.eqVec (Q.A j) (Q.A k) &&
          (ltStrict (Q.b j) (Q.b k) || (decide (j < k) && le (Q.b j) (Q.b k)))) = true
      ∧ (∀ c, toReal (Q.A k c) = toReal (Q.A i c)) ∧ toReal (Q.b k) ≤ toReal (Q.b i) := by
    intro i
    -- the rows with this normal and a no larger right-hand side, the least by `(b, index)`
    obtain ⟨j, hjS, hmin⟩ := (Finset.univ.filter fun j : Fin Q.m =>
        (∀ c, toReal (Q.A j c) = toReal (Q.A i c)) ∧
          toReal (Q.b j) ≤ toReal (Q.b i)).exists_min_image
      (fun j => toLex (toReal (Q.b j), j)) ⟨i, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjS hmin
    refine ⟨j, ?_, hjS⟩
    -- a row dominating it would be in the set and lexicographically smaller
    by_contra hk
    have hany : ((List.finRange Q.m).any fun j' =>
        HPolytope.eqVec (Q.A j') (Q.A j) &&
          (ltStrict (Q.b j') (Q.b j) || (decide (j' < j) && le (Q.b j') (Q.b j)))) = true := by
      by_contra h'
      exact hk (by simp [Bool.eq_false_iff.mpr h'])
    -- the dominating row, and what it gives
    obtain ⟨j', -, hj'⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hj'
    obtain ⟨heq, hd⟩ := hj'
    have hb : toReal (Q.b j') ≤ toReal (Q.b j) := by
      rcases hd with hd | ⟨-, hd⟩
      · exact (toReal_lt_of_ltStrict hd).le
      · exact toReal_le_of_le hd
    have hmem := hmin j' ⟨fun c => (HPolytope.toReal_eq_of_eqVec heq c).trans (hjS.1 c),
      hb.trans hjS.2⟩
    have hlt : toLex (toReal (Q.b j'), j') < toLex (toReal (Q.b j), j) := by
      rw [Prod.Lex.lt_iff]
      rcases hd with hd | ⟨hjj, -⟩
      · exact Or.inl (toReal_lt_of_ltStrict hd)
      · rcases hb.lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, hjj⟩
    exact absurd hmem (not_le.mpr hlt)
  -- the result keeps the rows with no dominator; the others follow from `key`
  unfold HPolytope.dropAligned
  ext x
  rw [HPolytope.mem_restrict_iff, HPolytope.mem_construct_iff]
  constructor
  · -- a deleted row is its kept dominator, whose value is the same
    rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun r => h2 r rfl⟩
    obtain ⟨k, hk, hA, hb⟩ := key i
    have hv : (toRealMat Q.A *ᵥ x) i = (toRealMat Q.A *ᵥ x) k := by
      simp only [mulVec, dotProduct, toRealMat]
      exact Finset.sum_congr rfl fun c _ => by rw [hA c]
    rw [hv]
    exact (h1 k hk).trans hb
  · rintro ⟨h1, h2⟩
    exact ⟨fun i _ => h1 i, fun r _ => h2 r⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
