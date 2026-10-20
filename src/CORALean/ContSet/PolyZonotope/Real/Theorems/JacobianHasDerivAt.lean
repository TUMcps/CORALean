module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Jacobian
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

/-!
# `PolyZonotope.jacobian` is the derivative of the dependent point

Moving the factor `k` along the line `t ↦ update a k t`, the point of the polynomial zonotope has
the derivative `point (jacobian k) a` at `t = aₖ`. Each monomial is `tᵉ` times the other factors'
powers, with derivative `e tᵉ⁻¹` times the same, which is the monomial of the lowered exponent
matrix; for `e = 0` both sides are `0` since the coefficient is `0` (the natural subtraction does
not matter there). In any real normed space, in particular `Vec ℝ n`, where the derivative is
taken in the sup norm.

## Inputs
* `pZ` – polynomial zonotope
* `k` – factor index
* `a` – factor values

## Hypotheses
* none

## Conclusion
* the derivative set's point is the derivative in that factor
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One monomial along the line is `tᵉ` times the other factors' powers. -/
theorem PolyZonotope.aux_monomial_update {p h : ℕ} (E : Fin p → Fin h → ℕ) (a : Fin p → ℝ)
    (k : Fin p) (t : ℝ) (i : Fin h) :
    PolyZonotope.monomial E (Function.update a k t) i
      = t ^ E k i * ∏ k' ∈ Finset.univ.erase k, a k' ^ E k' i := by -- --- PROOF ---
  unfold PolyZonotope.monomial
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), Function.update_self]
  -- off `k` the update reads `a`
  exact congrArg _ (Finset.prod_congr rfl fun k' hk' => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')])

/-- The lowered exponent matrix's monomial is the derivative's factor. -/
theorem PolyZonotope.aux_monomial_jacobian {p h : ℕ} (E : Fin p → Fin h → ℕ) (a : Fin p → ℝ)
    (k : Fin p) (i : Fin h) :
    PolyZonotope.monomial (fun k' i => if k' = k then E k i - 1 else E k' i) a i
      = a k ^ (E k i - 1) * ∏ k' ∈ Finset.univ.erase k, a k' ^ E k' i := by -- --- PROOF ---
  unfold PolyZonotope.monomial
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  beta_reduce
  rw [if_pos rfl]
  exact congrArg _ (Finset.prod_congr rfl fun k' hk' => by
    rw [if_neg (Finset.ne_of_mem_erase hk')])


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.jacobian_hasDerivAt (pZ : PolyZonotope α) (k : Fin pZ.p)
    (a : Fin pZ.p → ℝ) :
    HasDerivAt (fun t => pZ.point (Function.update a k t)) ((pZ.jacobian k).point a)
      (a k) := by -- --- PROOF ---
  -- each term of the sum is a monomial `tᵉ R` times a fixed generator
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin pZ.h)),
      HasDerivAt (fun t => PolyZonotope.monomial pZ.E (Function.update a k t) i • pZ.G i)
        (((pZ.E k i : ℝ) * PolyZonotope.monomial (pZ.jacobian k).E a i) • pZ.G i) (a k) := by
    intro i _
    have h1 := ((hasDerivAt_pow (pZ.E k i) (a k)).mul_const
      (∏ k' ∈ Finset.univ.erase k, a k' ^ pZ.E k' i)).smul_const (pZ.G i)
    simp only [PolyZonotope.aux_monomial_update]
    refine h1.congr_deriv ?_
    -- the lowered exponent matrix's monomial is `aₖᵉ⁻¹` times the same rest
    rw [show PolyZonotope.monomial (pZ.jacobian k).E a i
      = a k ^ (pZ.E k i - 1) * ∏ k' ∈ Finset.univ.erase k, a k' ^ pZ.E k' i from
        PolyZonotope.aux_monomial_jacobian pZ.E a k i, mul_assoc]
  have hsum := (HasDerivAt.fun_sum hterm).const_add pZ.c
  refine hsum.congr_deriv ?_
  -- the derivative's point is the sum of the scaled generators at the lowered monomials
  show _ = (0 : α) + ∑ i, PolyZonotope.monomial (pZ.jacobian k).E a i
    • ((pZ.E k i : ℝ) • pZ.G i)
  rw [zero_add]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
