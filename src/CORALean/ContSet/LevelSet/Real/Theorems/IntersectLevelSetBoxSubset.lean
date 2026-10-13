import CORALean.ContSet.LevelSet.Real.Operations.IntersectLevelSetBox

/-!
# `intersect(I, LS)` encloses the cut

[1, Thm. 1]'s enclosure: `I ∩ LS ⊆ {T(x) | x ∈ I}`, for every function `p_k` and with no
condition on the box. A point of the cut is its own image: there `x(k) = p_k(x)` already.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem intersectLevelSetBox_subset (I : Interval (Vec ℝ n)) (k : Fin n) (p : Vec ℝ n → ℝ) :
    I.construct ∩ {x | x k = p x} ⊆ (intersectLevelSetBox I k p).construct := by -- --- PROOF ---
  rintro x ⟨hxI, hxk⟩
  refine ⟨x, hxI, 0, fun i => ⟨le_rfl, le_rfl⟩, ?_⟩
  simp only [intersectLevelSetBox, add_zero]
  have hk : x k = p x := hxk
  rw [← hk, Function.update_eq_self]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
