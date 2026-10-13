import CORALean.ContSet.Interval.Real.Operations.ExploreBNVisits
import CORALean.ContSet.Interval.Real.Operations.FindSolutions

/-!
# `Interval.exploreBN`

[1, Alg. 2], `EXPLORE BN(B, α)`, on the ordered box `[0, b₁] × … × [0, bₙ]` and the hyperplane
`Σᵢ xᵢ = α`: starting from the face `(*, …, *)` (line 1), every vertex `w` the search visits
adds `FIND SOLUTIONS(w)` to `L` (line 8). The visits are `Interval.exploreBNVisits`.

## References

* [1] C. Lara, J. J. Flores and F. Calderon. "On the Hyperbox – Hyperplane Intersection
      Problem". INFOCOMP Journal of Computer Science, 8(4):21-27, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- `L`, the union of `FIND SOLUTIONS` over the visited vertices. -/
noncomputable def Interval.exploreBN (b : Vec ℝ n) (α : ℝ) : Finset (Vec ℝ n) :=
  (Interval.exploreBNVisits b α 0 fun _ => false).foldr
    (fun w L => Interval.findSolutions b α ((⟨0, b⟩ : Interval (Vec ℝ n)).corner w) ∪ L) ∅

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
