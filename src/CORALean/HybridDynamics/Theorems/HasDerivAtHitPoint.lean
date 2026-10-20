module

public import CORALean.HybridDynamics.Definitions.HitPoint
public import CORALean.HybridDynamics.Definitions.HitJacobian
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# `hitJacobian` is the first derivative of `hitPoint`

[1, Prop. 2], the first half, "obtained via standard derivation": along the `l`-th axis
`y_{h,i}(x₀ + s e_l) = x₀_i + sδ_il + (fᵢ + sA_il)(D - sn_l)/(Λ + sΥ_l)`, `f = Ax₀ + b`,
`D = d - nᵀx₀`, a quotient of affine functions of `s`, whose derivative at `0` is `L_il`.
`Λ(x₀) ≠ 0` is where `y_h` is defined at all.

## Inputs
* `A` – flow matrix
* `b` – flow offset
* `nv` – guard normal
* `x₀` – initial state
* `d` – guard offset
* `i` – output coordinate
* `l` – derivative axis

## Hypotheses
* `hΛ` – flow does not run parallel to the guard

## Conclusion
* the Jacobian entry is the derivative of the hit point

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

/-- [1, Prop. 2]: `∂y_{h,i}/∂x₀_l = L_il(x₀)`, wherever `Λ(x₀) = nᵀ(Ax₀ + b) ≠ 0`. -/
theorem GuardMap.hasDerivAt_hitPoint {A : Mat ℝ n n} {b nv x₀ : Vec ℝ n} {d : ℝ}
    (hΛ : nv ⬝ᵥ (A *ᵥ x₀ + b) ≠ 0) (i l : Fin n) :
    HasDerivAt (fun s : ℝ => GuardMap.hitPoint A b nv d (x₀ + s • Pi.single l 1) i)
      (GuardMap.hitJacobian A b nv d x₀ i l) 0 := by -- --- PROOF ---
  set f : Vec ℝ n := A *ᵥ x₀ + b with hfdef
  set Λ : ℝ := nv ⬝ᵥ f with hΛdef
  set D : ℝ := d - nv ⬝ᵥ x₀ with hDdef
  -- along the axis, every ingredient is affine in `s`
  have hform : (fun s : ℝ => GuardMap.hitPoint A b nv d (x₀ + s • Pi.single l 1) i)
      = fun s => (x₀ i + s * (Pi.single l 1 : Vec ℝ n) i)
        + (D - s * nv l) / (Λ + s * (nv ᵥ* A) l) * (f i + s * A i l) := by
    funext s
    simp only [GuardMap.hitPoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_add,
      Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, Matrix.mulVec_single_one,
      dotProduct_single_one, f, Λ, D]
    rw [show nv ⬝ᵥ col A l = (nv ᵥ* A) l from rfl, show col A l i = A i l from rfl]
    ring_nf
  rw [hform]
  -- the quotient rule at `s = 0`, then the paper's grouping
  have hnum : HasDerivAt (fun s : ℝ => D - s * nv l) (-nv l) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (nv l)).const_sub D
  have hden : HasDerivAt (fun s : ℝ => Λ + s * (nv ᵥ* A) l) ((nv ᵥ* A) l) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ((nv ᵥ* A) l)).const_add Λ
  have hf : HasDerivAt (fun s : ℝ => f i + s * A i l) (A i l) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (A i l)).const_add (f i)
  have hx : HasDerivAt (fun s : ℝ => x₀ i + s * (Pi.single l 1 : Vec ℝ n) i)
      ((Pi.single l 1 : Vec ℝ n) i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ((Pi.single l 1 : Vec ℝ n) i)).const_add (x₀ i)
  have h := hx.add ((hnum.div hden (by simpa using hΛ)).mul hf)
  refine h.congr_deriv ?_
  simp only [GuardMap.hitJacobian, Matrix.of_apply, ← hfdef, ← hΛdef, ← hDdef, Pi.div_apply,
    Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, zero_mul, sub_zero, add_zero,
    Pi.single_apply, Matrix.one_apply]
  field_simp
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
