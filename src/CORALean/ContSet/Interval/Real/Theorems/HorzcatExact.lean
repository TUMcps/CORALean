module

public import CORALean.ContSet.Interval.Real.Operations.Horzcat

@[expose] public section

/-!
# `Interval.horzcat` is exactly the set of side-by-side concatenations

A matrix lies in the concatenated box iff its left block is in the first box and its right block in
the second: no hypothesis, an empty operand gives an empty result and conversely.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {m n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.horzcat_exact (I : Interval (Mat ℝ m n₁)) (J : Interval (Mat ℝ m n₂)) :
    (I.horzcat J).construct =
      (fun p : Mat ℝ m n₁ × Mat ℝ m n₂ => fun i => Fin.append (p.1 i) (p.2 i)) ''
        (I.construct ×ˢ J.construct) := by -- --- PROOF ---
  ext B
  constructor
  · intro hB
    refine ⟨(fun i j => B i (Fin.castAdd n₂ j), fun i j => B i (Fin.natAdd n₁ j)),
      ⟨fun ⟨i, j⟩ => ?_, fun ⟨i, j⟩ => ?_⟩, ?_⟩
    · simpa [Interval.horzcat] using hB (i, Fin.castAdd n₂ j)
    · simpa [Interval.horzcat] using hB (i, Fin.natAdd n₁ j)
    · funext i
      exact Fin.append_castAdd_natAdd (f := B i)
  · rintro ⟨⟨A₁, A₂⟩, ⟨h₁, h₂⟩, rfl⟩ ⟨i, k⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simpa [Interval.horzcat] using h₁ (i, j)
    · simpa [Interval.horzcat] using h₂ (i, j)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
