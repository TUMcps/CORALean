module

public import CORALean.ContSet.Interval.Real.Operations.DiagVec

@[expose] public section

/-!
# `Interval.diagVec` is exactly the set of diagonals of the box

Reading a matrix box's diagonal is exact when no entry of the box is empty: with an empty
off-diagonal entry the box has no matrices at all, though its diagonal box may be nonempty.

## Inputs
* `I` – interval matrix

## Hypotheses
* `hI` – `I` has ordered bounds

## Conclusion
* the diagonal vector box is exactly the image of the diagonals
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.diagVec_exact (I : Interval (Mat ℝ n n))
    (hI : ∀ i j, I.inf i j ≤ I.sup i j) : -- --- CONCL ---
    I.diagVec.construct = (fun A i => A i i) '' I.construct := by -- --- PROOF ---
  ext x
  constructor
  · intro hx
    refine ⟨fun i j => if i = j then x i else I.inf i j, fun ⟨i, j⟩ => ?_, ?_⟩
    · by_cases hij : i = j
      · subst hij
        simp only [Entrywise.entry_mat, if_true]
        exact hx i
      · simpa [hij] using hI i j
    · funext i; simp
  · rintro ⟨A, hA, rfl⟩ i
    exact hA (i, i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
