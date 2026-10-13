import CORALean.ContSet.Zonotope.Real.Theorems.CentreMemConstruct
import CORALean.ContSet.HPolytope.Real.Operations.MemIneqsIff
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Module.Basic

/-!
# A degenerate zonotope has no polyhedral norm

`[1, Remark 2]` says that for a degenerate `Z`, where `‖·‖_Z` is not defined everywhere,
"`S_Z` is a norm, and can be used instead of `‖·‖_Z` to check whether a point lies in `Z`".
`S_Z` (`[1, Def. 3]`) needs a halfspace representation with every `hᵢ ≠ 0`, and a
degenerate `Z` centred at the origin has none: `0 ∈ Z` forces every `hᵢ > 0`, and then
`{H x < h}` is an open set around `0` inside `Z`. No norm can serve either, a norm's unit
ball having an interior.

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.not_exists_polyNorm_of_degenerate (Z : Zonotope (Vec ℝ n)) (hc : Z.c = 0)
    (hdeg : interior Z.construct = ∅) :
    ¬ ∃ (s : ℕ) (H : Mat ℝ s n) (h : Vec ℝ s), (∀ i, h i ≠ 0) ∧
      (HPolytope.ineqs H h).construct = Z.construct := by -- --- PROOF ---
  rintro ⟨s, H, h, hne, hrep⟩
  -- `0 ∈ Z` makes every right-hand side positive
  have h0 : (0 : Vec ℝ n) ∈ (HPolytope.ineqs H h).construct := by
    rw [hrep, ← hc]; exact Z.centre_mem_construct
  have hpos : ∀ i, 0 < h i := fun i => by
    have := HPolytope.mem_ineqs_iff.mp h0 i
    simp only [mulVec_zero, Pi.zero_apply] at this
    exact lt_of_le_of_ne this (hne i).symm
  -- so the strict inequalities cut out an open set around `0` inside `Z`
  have hopen : IsOpen {x : Vec ℝ n | ∀ i, (H *ᵥ x) i < h i} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt
      ((continuous_apply i).comp (Continuous.matrix_mulVec continuous_const continuous_id))
      continuous_const
  have hsub : {x : Vec ℝ n | ∀ i, (H *ᵥ x) i < h i} ⊆ Z.construct := fun x hx => by
    rw [← hrep]; exact HPolytope.mem_ineqs_iff.mpr fun i => (hx i).le
  have := interior_maximal hsub hopen (show (0 : Vec ℝ n) ∈ _ from fun i => by simpa using hpos i)
  rw [hdeg] at this
  exact this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
