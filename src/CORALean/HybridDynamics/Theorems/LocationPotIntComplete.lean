import CORALean.HybridDynamics.Operations.LocationPotInt

/-!
# `Location.potInt` lists every pair that meets

If a point lies in guard `i` and in reach set `j`, and transition `i` does not lead to
`finalLoc`, then `(i, j)` is listed. This is the direction CORA relies on: a skipped pair is
truly disjoint, given a sound `IsDisjoint`. The converse does not hold, a listed pair may be
disjoint.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S G : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (G n) (Vec ℝ n)]
variable {L 𝕋 : Type} [Scalar 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

omit [Scalar 𝕋] in
/-- A guard and a set sharing a point are listed together, unless the transition is skipped. -/
theorem Location.potInt_complete [DecidableEq L] [∀ n, IsDisjoint (G n) (S n)]
    (ℓ : Location S G L 𝕋 n) (Rs : List (S n)) (finalLoc : L) {i j : ℕ}
    (hi : i < ℓ.trans.length) (hj : j < Rs.length) (hfin : ℓ.trans[i].target ≠ finalLoc)
    {x : Vec ℝ n} (hg : x ∈ construct ℓ.trans[i].guard) (hR : x ∈ construct Rs[j]) :
    (i, j) ∈ ℓ.potInt Rs finalLoc := by -- --- PROOF ---
  -- the pair is not certified disjoint, since `x` lies in both
  have hnd : IsDisjoint.isDisjoint ℓ.trans[i].guard Rs[j] = false := by
    cases h : IsDisjoint.isDisjoint ℓ.trans[i].guard Rs[j]
    · rfl
    · exact absurd hg (Set.disjoint_left.mp (IsDisjoint.isDisjoint_sound _ _ h) hR)
  unfold Location.potInt
  rw [List.mem_flatMap]
  refine ⟨(ℓ.trans[i], i), ?_, ?_⟩
  · exact List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem hi])
  · simp only [hfin, if_false, List.mem_filterMap]
    refine ⟨(Rs[j], j), ?_, ?_⟩
    · exact List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem hj])
    · simp [hnd]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
