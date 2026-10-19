module

public import CORALean.ContSet.Interval.Real.Operations.Mask

@[expose] public section

/-!
# `Interval.mask` is exactly the image under masking

For a box with no empty entry, the masked box is the image of the box under zeroing the entries
outside the pattern: the in-pattern entries keep their ranges and the rest are the point `0`. This
is `tril` and `triu` at their patterns.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.mask_exact (keep : Fin m → Fin n → Prop) [∀ i j, Decidable (keep i j)]
    (I : Interval (Mat ℝ m n)) (hI : ∀ i j, I.inf i j ≤ I.sup i j) : -- --- CONCL ---
    (I.mask keep).construct =
      (fun (A : Mat ℝ m n) (i : Fin m) (j : Fin n) => if keep i j then A i j else 0) ''
        I.construct := by -- --- PROOF ---
  ext B
  constructor
  · intro hB
    refine ⟨fun i j => if keep i j then B i j else I.inf i j, fun ⟨i, j⟩ => ?_, ?_⟩
    · by_cases h : keep i j
      · have := hB (i, j)
        simpa [Interval.mask, h] using this
      · simpa [h] using hI i j
    · funext i j
      by_cases h : keep i j
      · simp [h]
      · have := hB (i, j)
        simp only [Interval.mask, Entrywise.entry_mat, if_neg h] at this
        simp [h, le_antisymm this.2 this.1]
  · rintro ⟨A, hA, rfl⟩ ⟨i, j⟩
    by_cases h : keep i j
    · simpa [Interval.mask, h] using hA (i, j)
    · simp [Interval.mask, h]


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
