module

public import CORALean.ContSet.Zonotope.Real.Theorems.UnitIntervalMulOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.QuadMapMatZonoOuter
public import CORALean.HybridDynamics.Theorems.HitHessianNumEqHitHessianMatZono
public import CORALean.HybridDynamics.Definitions.HitPoint
public import CORALean.HybridDynamics.Definitions.HitJacobian
public import CORALean.HybridDynamics.Definitions.HitHessianNum

@[expose] public section

/-!
# The second-order expansion of the hitting point is exact

`y_h(ξ + ν) = y_h(ξ) + L(ξ)ν + ½ φ (νᵀQ⁽ⁱ⁾(ξ)ν)ᵢ` with the one factor `φ = 1/(Λ(ξ)Λ(ξ + ν))`,
wherever `Λ(ξ) ≠ 0` and `Λ(ξ + ν) ≠ 0`: `y_h` is a ratio whose denominator `Λ` is affine, so its
Taylor series of [1, Prop. 3] ends at the second order with a remainder shared by every
coordinate, rather than one at a Lagrange point per coordinate. `νᵀQ⁽ⁱ⁾(ξ)ν = 2(Θᵀν)(Aν)ᵢ −
2(Θᵀν)(Υν)(Aξ + b)ᵢ/Λ`, `Ω` being skew. What `GuardMap.hitSet_subset_hitEnclosure` and
`Location.guardIntersectHyperplaneMap_outer` rest on.

## Inputs
* `A` – flow matrix
* `b` – flow offset
* `nv` – guard normal
* `d` – guard offset
* `ξ` – expansion point
* `ν` – displacement

## Hypotheses
* `hξ` – flow does not run parallel to the guard at the point
* `hx` – flow does not run parallel to the guard at the shifted point

## Conclusion
* the second-order expansion of the hit point is exact

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in Reachability
      Analysis of Hybrid Systems". Proceedings of the 15th ACM international conference on Hybrid
      Systems: Computation and Control, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `νᵀQ⁽ⁱ⁾(ξ)ν = 2(Θᵀν)(Aν)ᵢ − 2(Θᵀν)(Υν)(Aξ + b)ᵢ/Λ`: `Ω` is skew. -/
private theorem aux_hitPointAdd_quad (A : Mat ℝ n n) (b nv : Vec ℝ n) (d : ℝ) (ξ ν : Vec ℝ n)
    (i : Fin n) : -- --- CONCL ---
    ν ⬝ᵥ (GuardMap.hitHessianNum A b nv d ξ i *ᵥ ν) =
      2 * (A *ᵥ ν) i * ((-((nv ⬝ᵥ (A *ᵥ ξ + b)) • nv) - (d - nv ⬝ᵥ ξ) • (nv ᵥ* A)) ⬝ᵥ ν)
      - 2 * ((-((nv ⬝ᵥ (A *ᵥ ξ + b)) • nv) - (d - nv ⬝ᵥ ξ) • (nv ᵥ* A)) ⬝ᵥ ν)
        * ((nv ᵥ* A) ⬝ᵥ ν) * (A *ᵥ ξ + b) i / (nv ⬝ᵥ (A *ᵥ ξ + b)) := by -- --- PROOF ---
  set Λ : ℝ := nv ⬝ᵥ (A *ᵥ ξ + b)
  set Υ : Vec ℝ n := nv ᵥ* A
  set Θ : Vec ℝ n := -(Λ • nv) - (d - nv ⬝ᵥ ξ) • Υ
  set f : Vec ℝ n := A *ᵥ ξ + b
  have hM : GuardMap.hitHessianNum A b nv d ξ i =
      vecMulVec (fun l => A i l) Θ + vecMulVec Θ (fun l => A i l)
        + f i • (-vecMulVec nv Υ + vecMulVec Υ nv) - (2 * f i / Λ) • vecMulVec Θ Υ := by
    ext l m
    simp only [GuardMap.hitHessianNum, of_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.neg_apply, vecMulVec_apply, smul_eq_mul]
    ring
  have hrow : (fun l => A i l) ⬝ᵥ ν = (A *ᵥ ν) i := rfl
  rw [hM, sub_mulVec, add_mulVec, add_mulVec, smul_mulVec, smul_mulVec, add_mulVec, neg_mulVec]
  simp only [vecMulVec_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul, dotProduct_neg,
    smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  rw [dotProduct_comm ν (fun l => A i l), hrow, dotProduct_comm ν Θ, dotProduct_comm ν nv,
    dotProduct_comm ν Υ, dotProduct_comm nv ν]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 5.4], exactly: `y_h(ξ + ν) = y_h(ξ) + L(ξ)ν + ½ φ (νᵀQ⁽ⁱ⁾(ξ)ν)ᵢ`,
`φ = 1/(Λ(ξ)Λ(ξ + ν))`. -/
theorem GuardMap.hitPoint_add_eq (A : Mat ℝ n n) (b nv : Vec ℝ n) (d : ℝ) (ξ ν : Vec ℝ n)
    (hξ : nv ⬝ᵥ (A *ᵥ ξ + b) ≠ 0) (hx : nv ⬝ᵥ (A *ᵥ (ξ + ν) + b) ≠ 0) : -- --- CONCL ---
    GuardMap.hitPoint A b nv d (ξ + ν) = GuardMap.hitPoint A b nv d ξ
      + GuardMap.hitJacobian A b nv d ξ *ᵥ ν
      + (1 / 2 : ℝ) • ((1 / ((nv ⬝ᵥ (A *ᵥ ξ + b)) * (nv ⬝ᵥ (A *ᵥ (ξ + ν) + b)))) •
        fun i => ν ⬝ᵥ (GuardMap.hitHessianNum A b nv d ξ i *ᵥ ν)) := by -- --- PROOF ---
  -- `L(ξ) = I + (d - nᵀξ)/Λ · A + (Ax + b)Θᵀ/Λ²`
  have hJ : GuardMap.hitJacobian A b nv d ξ = 1 + ((d - nv ⬝ᵥ ξ) / nv ⬝ᵥ (A *ᵥ ξ + b)) • A
      + (1 / (nv ⬝ᵥ (A *ᵥ ξ + b)) ^ 2) • vecMulVec (A *ᵥ ξ + b)
        (-((nv ⬝ᵥ (A *ᵥ ξ + b)) • nv) - (d - nv ⬝ᵥ ξ) • (nv ᵥ* A)) := by
    ext i l
    simp only [GuardMap.hitJacobian, of_apply, Matrix.add_apply, Matrix.smul_apply,
      vecMulVec_apply, smul_eq_mul]
    ring
  -- the quadratic form and `Θ(ξ)ᵀν = -Λ(ξ)nᵀν - (d - nᵀξ)Υν`
  have hq : (fun i => ν ⬝ᵥ (GuardMap.hitHessianNum A b nv d ξ i *ᵥ ν)) = fun i =>
      2 * (A *ᵥ ν) i * ((-((nv ⬝ᵥ (A *ᵥ ξ + b)) • nv) - (d - nv ⬝ᵥ ξ) • (nv ᵥ* A)) ⬝ᵥ ν)
      - 2 * ((-((nv ⬝ᵥ (A *ᵥ ξ + b)) • nv) - (d - nv ⬝ᵥ ξ) • (nv ᵥ* A)) ⬝ᵥ ν)
        * ((nv ᵥ* A) ⬝ᵥ ν) * (A *ᵥ ξ + b) i / (nv ⬝ᵥ (A *ᵥ ξ + b)) :=
    funext fun i => aux_hitPointAdd_quad A b nv d ξ ν i
  have hT : (-((nv ⬝ᵥ (A *ᵥ ξ + b)) • nv) - (d - nv ⬝ᵥ ξ) • (nv ᵥ* A)) ⬝ᵥ ν
      = -((nv ⬝ᵥ (A *ᵥ ξ + b)) * (nv ⬝ᵥ ν)) - (d - nv ⬝ᵥ ξ) * ((nv ᵥ* A) ⬝ᵥ ν) := by
    rw [sub_dotProduct, neg_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
      smul_eq_mul]
  -- `A(ξ + ν) + b`, `nᵀ(ξ + ν)` and `Λ(ξ + ν) = Λ(ξ) + Υν`
  have e1 : A *ᵥ (ξ + ν) + b = (A *ᵥ ξ + b) + A *ᵥ ν := by rw [mulVec_add]; abel
  have e3 : nv ⬝ᵥ ((A *ᵥ ξ + b) + A *ᵥ ν) = nv ⬝ᵥ (A *ᵥ ξ + b) + (nv ᵥ* A) ⬝ᵥ ν := by
    rw [dotProduct_add, dotProduct_mulVec]
  have e2 : nv ⬝ᵥ (ξ + ν) = nv ⬝ᵥ ξ + nv ⬝ᵥ ν := dotProduct_add _ _ _
  rw [e1, e3] at hx ⊢
  rw [hJ, hq]
  funext i
  simp only [GuardMap.hitPoint, add_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, e1, e2, e3, hT, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  -- one identity of rational functions in the scalars left
  generalize nv ⬝ᵥ (A *ᵥ ξ + b) = Λ at *
  generalize (nv ᵥ* A) ⬝ᵥ ν = δ at *
  generalize nv ⬝ᵥ ξ = nξ at *
  generalize nv ⬝ᵥ ν = η at *
  generalize (A *ᵥ ν) i = Aν at *
  generalize (A *ᵥ ξ) i = f₁ at *
  field_simp
  ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
