module

public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The weighted generators of a Minkowski sum

The generators of `Z₁ ⊕ Z₂` are those of `Z₁` followed by those of `Z₂` ([1, Prop. 1]), so a
weighted sum of them is the weighted sum over `Z₁` plus that over `Z₂`, whose weights start at
the index `Z₁.h`: the layout of the generators that [1, Prop. 1] indexes by tuples.

## Inputs
* `Z₁` – first zonotope
* `Z₂` – second zonotope
* `f` – generator weights

## Hypotheses
* none

## Conclusion
* the weighted generators of the sum are the sum of both parts

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.sumGen_plus (Z₁ Z₂ : Zonotope α) (f : ℕ → ℝ) :
    ∑ k : Fin (Z₁.plus Z₂).h, f k • (Z₁.plus Z₂).G k
      = ∑ k : Fin Z₁.h, f k • Z₁.G k + ∑ k : Fin Z₂.h, f (Z₁.h + k) • Z₂.G k := by -- --- PROOF ---
  refine (Fin.sum_univ_add (fun k : Fin (Z₁.h + Z₂.h) => f k • (Z₁.plus Z₂).G k)).trans ?_
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [Zonotope.plus, Fin.append_left]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [Zonotope.plus, Fin.append_right]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
