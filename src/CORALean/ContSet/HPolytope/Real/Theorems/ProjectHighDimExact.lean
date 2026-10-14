module

public import CORALean.ContSet.HPolytope.Real.Operations.ProjectHighDim
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.Basic
public import CORALean.ContSet.HPolytope.Real.Theorems.MemIntersection

@[expose] public section

/-!
# `projectHighDim` is the lift with the new coordinates zero, exactly

A point is in the result iff its coordinates `dims` form a point of `P` and every coordinate
`dims` does not hit is zero. For an injective `dims` that is the zero-padded image of `P`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.projectHighDim_exact (P : HPolytope (Vec ℝ n)) (dims : Fin n → Fin N) :
    (P.projectHighDim dims).construct
      = {x | (fun k => x (dims k)) ∈ P.construct
          ∧ ∀ j, (∀ k, dims k ≠ j) → x j = 0} := by -- --- PROOF ---
  classical
  ext x
  unfold HPolytope.projectHighDim
  dsimp only
  rw [HPolytope.mem_intersection_iff, HPolytope.lift_exact, HPolytope.mem_eqs_iff]
  -- a unit row reads one coordinate
  have hrow : ∀ (q : ℕ) (a : Fin q → Fin N) (r : Fin q),
      ((fun r j => if j = a r then (1 : ℝ) else 0 : Mat ℝ q N) *ᵥ x) r = x (a r) := by
    intro q a r
    simp [Matrix.mulVec, dotProduct]
  simp only [hrow]
  refine and_congr Iff.rfl ⟨fun h j hj => ?_, fun h r => ?_⟩
  · -- a coordinate `dims` misses is one of the numbered new ones
    have hmem : j ∈ Finset.univ.filter fun j : Fin N => ∀ k, dims k ≠ j := by simpa using hj
    obtain ⟨r, hr⟩ := (Finset.orderIsoOfFin _ rfl).surjective ⟨j, hmem⟩
    have := h r
    rw [show (Finset.orderIsoOfFin _ rfl r).1 = j from by rw [hr]] at this
    exact this
  · exact h _ (Finset.mem_filter.mp ((Finset.orderIsoOfFin _ rfl) r).2).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
