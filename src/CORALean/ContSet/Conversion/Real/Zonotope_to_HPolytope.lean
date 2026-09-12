import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.ContSet.HPolytope.Real.Operations.OfBounds
import CORALean.ContSet.HPolytope.Real.Operations.SubsetOfBounds

/-!
# A zonotope as halfspaces

A zonotope answers a direction without a linear program: the centre's value plus
the sum of what each generator can contribute in absolute value, every generator
independently free to take its own sign. That is exact and costs one dot product
per generator, which is why `SupportBound` is where the two representations
meet.

The rows are the caller's, as always. Exact when they are the zonotope's own
facet normals, of which there are `2·C(h, n-1)` — the reason CORA does not
convert a zonotope to halfspaces unless it has to.

`supportBound` is the `d̃` of [1, Prop. 4], where a halfspace description
absorbs a zonotope without enumerating either one's vertices.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation".
      arXiv:2310.19083, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {q : ℕ}

/-- The support function itself, attained rather than approached. -/
def Zonotope.supportBound (Z : Zonotope α) (c : α →ₗ[ℝ] ℝ) : SupportBound Z.construct c where
  val := c Z.c + ∑ j, |c (Z.G j)|
  le := by
    rintro _ ⟨β, hβ, rfl⟩
    rw [map_add, map_sum]
    refine add_le_add le_rfl (Finset.sum_le_sum fun j _ => ?_)
    rw [map_smul, smul_eq_mul]
    calc β j * c (Z.G j) ≤ |β j * c (Z.G j)| := le_abs_self _
      _ = |β j| * |c (Z.G j)| := abs_mul _ _
      _ ≤ 1 * |c (Z.G j)| := mul_le_mul_of_nonneg_right (hβ j) (abs_nonneg _)
      _ = |c (Z.G j)| := one_mul _

def Zonotope.hPolytope (Z : Zonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) : HPolytope α :=
  HPolytope.ofBounds Aq fun i => Z.supportBound (Aq i)


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.hPolytope_contains (Z : Zonotope α) (Aq : Fin q → (α →ₗ[ℝ] ℝ)) :
    Z.construct ⊆ (Z.hPolytope Aq).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
