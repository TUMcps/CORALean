module

public import CORALean.HybridDynamics.Definitions.HitJacobian
public import CORALean.HybridDynamics.Definitions.HitHessian
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# `hitHessian` is the derivative of `hitJacobian`

[1, Prop. 2], the second half: `Q̃⁽ⁱ⁾_lm = ∂²y_{h,i}/∂x₀_l∂x₀_m`, here as the derivative of
`L_im` along the `l`-th axis. Along it `Λ`, `d - nᵀx₀`, `Θ_m` and `(Ax₀ + b)ᵢ` are affine in
`s`, and the quotient rule gives `(A_im Θ_l + A_il Θ_m + (Ω_ml - 2Θ_mΥ_l/Λ)fᵢ)/Λ²`. That is the
printed `Q⁽ⁱ⁾_lm/Λ²`, whose bracket has `l` and `m` the other way round, because
`Ω_ml - Ω_lm = 2(Θ_mΥ_l - Θ_lΥ_m)/Λ` — the symmetry of second derivatives, which `ring` checks.
Prop. 2 states the derivative of `y_h` twice; `hasDerivAt_deriv_hitPoint` composes this with
`hasDerivAt_hitPoint` to state exactly that.

## Inputs
* `A` – flow matrix
* `b` – flow offset
* `nv` – guard normal
* `x₀` – initial state
* `d` – guard offset
* `i` – output coordinate
* `l` – derivative axis
* `m` – Jacobian column

## Hypotheses
* `hΛ` – flow does not run parallel to the guard

## Conclusion
* the Hessian entry is the derivative of the Jacobian entry

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 2]: `∂L_im/∂x₀_l = Q̃⁽ⁱ⁾_lm(x₀)`, wherever `Λ(x₀) ≠ 0`. -/
theorem GuardMap.hasDerivAt_hitJacobian {A : Mat ℝ n n} {b nv x₀ : Vec ℝ n} {d : ℝ}
    (hΛ : nv ⬝ᵥ (A *ᵥ x₀ + b) ≠ 0) (i l m : Fin n) :
    HasDerivAt (fun s : ℝ => GuardMap.hitJacobian A b nv d (x₀ + s • Pi.single l 1) i m)
      (GuardMap.hitHessian A b nv d x₀ i l m) 0 := by -- --- PROOF ---
  set f : Vec ℝ n := A *ᵥ x₀ + b with hfdef
  set Λ : ℝ := nv ⬝ᵥ f with hΛdef
  set D : ℝ := d - nv ⬝ᵥ x₀ with hDdef
  set Υ : Vec ℝ n := nv ᵥ* A with hΥdef
  -- along the axis, `Λ`, `D`, `fᵢ` and `Θ_m` are affine in `s`
  have hform : (fun s : ℝ => GuardMap.hitJacobian A b nv d (x₀ + s • Pi.single l 1) i m)
      = fun s => (1 : Mat ℝ n n) i m + A i m / (Λ + s * Υ l) * (D - s * nv l)
        + (f i + s * A i l) * (-((Λ + s * Υ l) * nv m) - (D - s * nv l) * Υ m)
          / (Λ + s * Υ l) ^ 2 := by
    funext s
    simp only [GuardMap.hitJacobian, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.sub_apply, Pi.neg_apply, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
      dotProduct_smul, Matrix.mulVec_single_one, dotProduct_single_one, hfdef, hΛdef, hDdef, hΥdef]
    rw [show nv ⬝ᵥ col A l = (nv ᵥ* A) l from rfl, show col A l i = A i l from rfl]
    ring_nf
  rw [hform]
  have hlin : ∀ c k : ℝ, HasDerivAt (fun s : ℝ => c + s * k) k 0 := fun c k => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const k).const_add c
  have hden := hlin Λ (Υ l)
  have hnum : HasDerivAt (fun s : ℝ => D - s * nv l) (-nv l) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (nv l)).const_sub D
  have hΘ : HasDerivAt (fun s : ℝ => -((Λ + s * Υ l) * nv m) - (D - s * nv l) * Υ m)
      (-(Υ l * nv m) - -nv l * Υ m) 0 :=
    ((hden.mul_const (nv m)).neg).sub (hnum.mul_const (Υ m))
  -- the quotient rule, term by term, at `s = 0`
  have hΛ0 : Λ + 0 * Υ l ≠ 0 := by simpa using hΛ
  have h := ((hasDerivAt_const (0 : ℝ) ((1 : Mat ℝ n n) i m)).add
    (((hasDerivAt_const (0 : ℝ) (A i m)).div hden hΛ0).mul hnum)).add
    (((hlin (f i) (A i l)).mul hΘ).div (hden.pow 2) (pow_ne_zero 2 hΛ0))
  refine h.congr_deriv ?_
  simp only [GuardMap.hitHessian, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, ← hfdef,
    ← hΛdef, ← hDdef, ← hΥdef, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Matrix.neg_apply,
    Matrix.add_apply, vecMulVec_apply, zero_mul, sub_zero, add_zero, Pi.div_apply, Pi.pow_apply,
    Pi.mul_apply]
  field_simp
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
