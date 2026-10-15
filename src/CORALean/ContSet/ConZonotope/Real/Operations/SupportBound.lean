module

public import CORALean.ContSet.ConZonotope.Real.Operations.Domain
public import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructEqImage
public import CORALean.ContSet.HPolytope.Real.Operations.SupportBound

@[expose] public section

/-!
# `ConZonotope.supportBound`

CORA's `@conZonotope/supportFunc_` (`supportFunc_linprog`) [1]: the support function of
`c + G ξ`, `|ξ| ≤ 1`, `A ξ = b`, in the direction `d`, is `d·c` plus the value of the linear
program `max (Gᵀd)·ξ` over the coefficient polytope `ConZonotope.domain`. The bound is the one
`HPolytope.supportBound` certifies for that program, so `none` where the pivot budget runs out
or the program is unbounded, and a bound where CORA returns the value: the bound is an upper
bound, equal to the supremum only when the dual solution is optimal, which is not claimed. CORA's
`'lower'` and `'range'` types, and the point attaining the value, are not modelled.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The program's objective `ξ ↦ c (G ξ)`, as a functional on the coefficient space. -/
def aux_conZonotopeObjective (cZ : ConZonotope α) (c : α →ₗ[ℝ] ℝ) : Vec ℝ cZ.h →ₗ[ℝ] ℝ :=
  ∑ j, c (cZ.G j) • LinearMap.proj j


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `c` of the center plus a certified bound of the coefficient program. -/
noncomputable def ConZonotope.supportBound (cZ : ConZonotope α) (c : α →ₗ[ℝ] ℝ) :
    Option (SupportBound cZ.construct c) :=
  (cZ.domain.supportBound (aux_conZonotopeObjective cZ c)).map fun u =>
    { val := c cZ.c + u.val
      le := by
        intro x hx
        rw [ConZonotope.construct_eq_image] at hx
        obtain ⟨β, hβ, rfl⟩ := hx
        have h1 := u.le β hβ
        have h2 : c (cZ.c + ∑ j, β j • cZ.G j) = c cZ.c + aux_conZonotopeObjective cZ c β := by
          rw [map_add, map_sum]
          simp only [map_smul, smul_eq_mul, aux_conZonotopeObjective, LinearMap.sum_apply,
            LinearMap.smul_apply, LinearMap.proj_apply]
          exact congrArg _ (Finset.sum_congr rfl fun j _ => mul_comm _ _)
        rw [h2]
        linarith }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
