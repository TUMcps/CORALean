import CORALean.ContSet.HPolytope.Real.Operations.RowsRhs
import Mathlib.Tactic.Linarith

/-!
# A point is in a polytope iff every row holds

`rows` lists the inequality rows and each equality row once with either sign, `rowsRhs` their
right-hand sides: `x ∈ P` iff `rowᵢ x ≤ rhsᵢ` for every `i`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_construct_iff_rows {P : HPolytope α} {x : α} :
    x ∈ P.construct ↔ ∀ i, P.rows i x ≤ P.rowsRhs i := by -- --- PROOF ---
  -- the rows and right-hand sides, read off at each of the three blocks
  have r1 : ∀ j, P.rows (Fin.castAdd _ j) = P.A j := fun j => Fin.append_left _ _ j
  have r2 : ∀ j, P.rows (Fin.natAdd P.m (Fin.castAdd P.me j)) = P.Ae j := fun j => by
    unfold HPolytope.rows; rw [Fin.append_right, Fin.append_left]
  have r3 : ∀ j, P.rows (Fin.natAdd P.m (Fin.natAdd P.me j)) = -P.Ae j := fun j => by
    unfold HPolytope.rows; rw [Fin.append_right, Fin.append_right]
  have s1 : ∀ j, P.rowsRhs (Fin.castAdd _ j) = P.b j := fun j => Fin.append_left _ _ j
  have s2 : ∀ j, P.rowsRhs (Fin.natAdd P.m (Fin.castAdd P.me j)) = P.be j := fun j => by
    unfold HPolytope.rowsRhs; rw [Fin.append_right, Fin.append_left]
  have s3 : ∀ j, P.rowsRhs (Fin.natAdd P.m (Fin.natAdd P.me j)) = -P.be j := fun j => by
    unfold HPolytope.rowsRhs; rw [Fin.append_right, Fin.append_right]
  constructor
  · -- a point of the polytope satisfies the three blocks of rows
    rintro ⟨hA, hAe⟩ i
    refine Fin.addCases (fun j => ?_) (fun i => ?_) i
    · rw [r1, s1]; exact hA j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [r2, s2]; exact (hAe j).le
      · rw [r3, s3]; simp [hAe j]
  · -- the two opposite rows of an equality give it
    intro h
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have := h (Fin.castAdd _ j)
      rwa [r1, s1] at this
    · have h1 := h (Fin.natAdd P.m (Fin.castAdd P.me j))
      have h2 := h (Fin.natAdd P.m (Fin.natAdd P.me j))
      rw [r2, s2] at h1
      rw [r3, s3] at h2
      simp only [LinearMap.neg_apply] at h2
      linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
