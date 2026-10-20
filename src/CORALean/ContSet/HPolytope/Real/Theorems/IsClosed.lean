module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import Mathlib.Analysis.RCLike.Lemmas

@[expose] public section

/-!
# A halfspace description is closed

An intersection of closed halfspaces and hyperplanes, one per constraint. A
constraint is any linear functional, and every linear functional on a
finite-dimensional space is continuous — which is why this is stated at `Vec`
rather than at any module.

Not bounded: unbounded halfspace descriptions are exactly what the
representation admits and a vertex description cannot.

## Inputs
* `P` – H-polytope

## Hypotheses
* none

## Conclusion
* A halfspace description is closed
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isClosed_construct (P : HPolytope (Vec ℝ n)) : -- --- CONCL ---
    IsClosed P.construct := by -- --- PROOF ---
  have hinter : P.construct = (⋂ i, {x : Vec ℝ n | P.A i x ≤ P.b i})
      ∩ ⋂ i, {x : Vec ℝ n | P.Ae i x = P.be i} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact Iff.rfl
  rw [hinter]
  refine IsClosed.inter (isClosed_iInter fun i => ?_) (isClosed_iInter fun i => ?_)
  · exact isClosed_le (P.A i).continuous_of_finiteDimensional continuous_const
  · exact isClosed_eq (P.Ae i).continuous_of_finiteDimensional continuous_const

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
