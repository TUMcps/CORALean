module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The segment from the origin to a point, without a `segment` field

`linComb (ofPoint 0) (ofPoint v)` already contains every `lam • v`: `segments
{0} {v}` is exactly `{(1 - lam) • v}`, witnessed at `1 - lam`. So a
representation with `LinComb` and `OfPoint` gets the segment for free, and no
class has to carry a `segment` field of its own.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S α : Type} [AddCommGroup α] [Module ℝ α] [ContSet S α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The segment from the origin to `v`, read off `linComb` and `ofPoint`
alone: witness `1 - lam` in `segments`, then `linComb_outer`. -/
theorem smul_mem_linComb_ofPoint [LinComb S α] [OfPoint S α] (v : α)
    {lam : ℝ} (hlam : lam ∈ Set.Icc (0:ℝ) 1) :
    lam • v ∈ construct (LinComb.linComb (S := S)
      (OfPoint.ofPoint (0 : α)) (OfPoint.ofPoint v)) := by
  refine LinComb.linComb_outer _ _ ⟨0, OfPoint.mem_ofPoint 0, v, OfPoint.mem_ofPoint v,
    1 - lam, ⟨by linarith [hlam.2], by linarith [hlam.1]⟩, ?_⟩
  match_scalars
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
