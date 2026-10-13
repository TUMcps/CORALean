import CORALean.ContSet.Interval.Float.Operations.Point

/-!
# The point interval contains its point, over a floating-point scalar

Split out from `Operations/Point.lean`, which used to carry both: one
declaration per file (issue #62) does not make an exception for a fact this
short. Nothing is rounded here; `mem_point` just reads the stored point back
through `RealImage.realImage`, generic over the ambient type as `point` itself
is, so it reaches `matPow`'s identity at `Mat 𝕋 n n` too.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =======================================  MAIN THEOREM  ======================================= --

-- both bounds are the stored value, so each coordinate is bounded by equality
theorem Interval.mem_point {α β ι : Type} [RealImage α β] [AddCommGroup β] [Module ℝ β]
    [Entrywise β ι] (v : α) :
    RealImage.realImage v ∈ (Interval.point v).construct := fun _ => ⟨le_rfl, le_rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
