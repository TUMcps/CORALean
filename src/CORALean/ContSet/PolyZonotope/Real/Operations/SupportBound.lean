module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
public import CORALean.Global.SupportFunction.SupportFunction
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# `PolyZonotope.supportBound`

[1, Prop. 7]: a direction sees the set as its dependent part plus its independent one. The
independent block answers exactly, `∑ⱼ |c (GI j)|`, and the dependent block is `point` over
the factor box, a polynomial range with no closed form. So the range bound is an argument:
`u` bounds `subsetAt` over that box, what the paper's `B(w(α), [-1,1])` returns, and whatever
produced it stays outside the trusted base as every `SupportBound` here does. Interval
arithmetic, Bernstein polynomials and verified global optimization are admissible sources; the
bound is exactly as tight as `u`. The value bounds the set and does not describe it.

## Inputs
* `pZ` – polynomial zonotope
* `c` – linear functional
* `u` – support bound of the factor part

## Output
* support bound of the set

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The dependent part's bound `u`, plus the independent block's own exact
extent in the direction `c`. -/
noncomputable def PolyZonotope.supportBound (pZ : PolyZonotope α) (c : α →ₗ[ℝ] ℝ)
    (u : SupportBound (pZ.subsetAt {a | ∀ k, |a k| ≤ 1}) c) : SupportBound pZ.construct c where
  val := u.val + ∑ j, |c (pZ.GI j)|
  le := by
    rintro _ ⟨a, β, ha, hβ, rfl⟩
    -- the dependent part is a point of `subsetAt`, which is what `u` bounds
    have hdep : c (pZ.point a) ≤ u.val := u.le _ ⟨a, ha, rfl⟩
    -- each independent coefficient is at most one in absolute value
    have hind : c (∑ j, β j • pZ.GI j) ≤ ∑ j, |c (pZ.GI j)| := by
      rw [map_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [map_smul, smul_eq_mul]
      calc β j * c (pZ.GI j) ≤ |β j * c (pZ.GI j)| := le_abs_self _
        _ = |β j| * |c (pZ.GI j)| := abs_mul _ _
        _ ≤ 1 * |c (pZ.GI j)| := mul_le_mul_of_nonneg_right (hβ j) (abs_nonneg _)
        _ = |c (pZ.GI j)| := one_mul _
    -- the two halves add, `point` being the first of them
    have hx : c (pZ.point a + ∑ j, β j • pZ.GI j) ≤ u.val + ∑ j, |c (pZ.GI j)| := by
      rw [map_add]
      exact add_le_add hdep hind
    exact hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
