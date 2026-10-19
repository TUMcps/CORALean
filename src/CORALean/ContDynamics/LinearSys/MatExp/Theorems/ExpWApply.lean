module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpW
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTerm
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# `W(t)`, entry by entry, in the shape [1, Prop. 4] evaluates

The rearrangement itself, with no interval anywhere: the `k ∈ {i, j}` part of
the row-column sum is pulled out and folded into the factor multiplying
`M i j`, leaving `k ≠ i, j` behind. On the diagonal the two pulled-out terms
coincide and become `γ (M i i)` instead.

This is the only algebra in [1, Prop. 4]; enclosure and tightness are then
the same statement about each of the three pieces, which is why both
`expW_mem_expIntervalW` and `expIntervalW_attained` go through here.

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `W(t)`'s entry `(i, j)`, split the way [1, Prop. 4] evaluates it. -/
theorem MatExp.expW_apply (M : Mat ℝ n n) (t : ℝ) (i j : Fin n) : -- --- CONCL ---
    MatExp.expW M t i j
      = (if i = j then MatExp.quadTerm t (M i i)
          else M i j * (t + t ^ 2 / 2 * (M i i + M j j)))
        + t ^ 2 / 2
          * ∑ k ∈ Finset.univ \ ({i, j} : Finset (Fin n)), M i k * M k j := by -- --- PROOF ---
  -- the two index sets the row-column sum splits into
  have hsum : ∑ k ∈ Finset.univ \ ({i, j} : Finset (Fin n)), M i k * M k j
      + ∑ k ∈ ({i, j} : Finset (Fin n)), M i k * M k j
      = ∑ k, M i k * M k j := Finset.sum_sdiff (Finset.subset_univ _)
  have hW : MatExp.expW M t i j = t * M i j + t ^ 2 / 2 * ∑ k, M i k * M k j := by
    simp [MatExp.expW, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  rw [hW, ← hsum]
  by_cases h : i = j
  · -- on the diagonal the pair collapses to one term, which is `γ`
    subst h
    have hpair : ({i, i} : Finset (Fin n)) = {i} := by simp
    rw [if_pos rfl, hpair, Finset.sum_singleton, MatExp.quadTerm]
    ring
  · rw [if_neg h, Finset.sum_pair h]
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
