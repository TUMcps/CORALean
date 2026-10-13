import CORALean.ContSet.Interval.Real.Operations.Vertcat

/-!
# `Interval.vertcat` is exactly the set of stacked matrices

A matrix lies in the stacked box iff its top block is in the first box and its bottom block in the
second: no hypothesis.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


variable {m₁ m₂ n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.vertcat_exact (I : Interval (Mat ℝ m₁ n)) (J : Interval (Mat ℝ m₂ n)) :
    (I.vertcat J).construct = (fun p : Mat ℝ m₁ n × Mat ℝ m₂ n => Fin.append p.1 p.2) ''
      (I.construct ×ˢ J.construct) := by -- --- PROOF ---
  ext B
  constructor
  · intro hB
    refine ⟨(fun i j => B (Fin.castAdd m₂ i) j, fun i j => B (Fin.natAdd m₁ i) j),
      ⟨fun ⟨i, j⟩ => ?_, fun ⟨i, j⟩ => ?_⟩, ?_⟩
    · simpa [Interval.vertcat] using hB (Fin.castAdd m₂ i, j)
    · simpa [Interval.vertcat] using hB (Fin.natAdd m₁ i, j)
    · exact Fin.append_castAdd_natAdd (f := B)
  · rintro ⟨⟨A₁, A₂⟩, ⟨h₁, h₂⟩, rfl⟩ ⟨k, j⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa [Interval.vertcat] using h₁ (i, j)
    · simpa [Interval.vertcat] using h₂ (i, j)


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
