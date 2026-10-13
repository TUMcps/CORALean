import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Tactic.Module

/-!
# A zonotope is centrally symmetric

`x ↦ 2c - x` negates the coefficients, so a point of the zonotope is sent to a point of it
([1, Sec. 2.1]: "a zonotope is a centrally symmetric polytope").

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems
      Reachability Analysis". In Hybrid Systems: Computation and Control (HSCC), LNCS 4981,
      Springer, 2008, pp. 215-228.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.central_symm_mem_construct (Z : Zonotope α) {x : α} (hx : x ∈ Z.construct) :
    (2 : ℝ) • Z.c - x ∈ Z.construct := by
  obtain ⟨β, hβ, rfl⟩ := hx
  refine ⟨fun j => -β j, fun j => by simpa using hβ j, ?_⟩
  simp only [neg_smul, Finset.sum_neg_distrib]
  module

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
