import CORALean.ContSet.Ellipsoid.Real.Operations.MinkDiffPoint
import CORALean.ContSet.ContSet.ContSet

/-!
# The Minkowski difference of an ellipsoid and a point is exactly the shifted ellipsoid

`x + s ∈ E` iff `x ∈ E` shifted by `-s`: every `E` and every `s`, degenerate ones included. Exact
(an equality of sets), for the vector branch of CORA's `minkDiff` only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.minkDiffPoint_exact (E : Ellipsoid n) (s : Vec ℝ n) :
    (E.minkDiffPoint s).construct = minkowskiDiff E.construct {s} := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩ y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨u, hu, by simp only [Ellipsoid.minkDiffPoint]; abel⟩
  · intro h
    obtain ⟨u, hu, hx⟩ := h s rfl
    exact ⟨u, hu, by
      simp only [Ellipsoid.minkDiffPoint]
      rw [sub_add_eq_add_sub]
      exact eq_sub_of_add_eq hx⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
