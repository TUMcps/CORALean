module

public import CORALean.ContSet.Zonotope.Float.Operations.QuadMapMatZono
public import CORALean.ContSet.Zonotope.Float.Theorems.AbsLeAbsBoundError
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.QuadMapOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.SumTermsMem
public import CORALean.ContSet.Zonotope.Float.Theorems.UnitIntervalMulOuter
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeZonotopeContains

@[expose] public section

/-!
# The float `quadMapMatZono` encloses the quadratic map over the matrix zonotopes

`Real.Zonotope.quadMapMatZono_outer` at float zonotopes and interval-matrix centers: for
`x ∈ Z`, centers `Dᵣ⁽ⁱ⁾` in the interval matrices `D⁽ⁱ⁾` and one factor `βⱼ ∈ [-1, 1]` per
generator shared by all `i` [1, Thm. 1], `(xᵀ(Dᵣ⁽ⁱ⁾ + ∑ⱼ βⱼK⁽ⁱ'ʲ⁾)x)ᵢ` is in the result: it is
`xᵀD̲⁽ⁱ⁾x`, a point of `Z_D` (`Zonotope.quadMap_outer`), plus `∑ⱼ βⱼ xᵀK⁽ⁱ'ʲ⁾x`, a point of the
sum of the `[-1, 1] ⊗ Z_K(j)` (`Zonotope.unitIntervalMul_outer`), plus `xᵀ(Dᵣ⁽ⁱ⁾ − D̲⁽ⁱ⁾)x`,
whose modulus is at most `∑ₗₖ |xₗ| (Dᵣ − D̲)ₗₖ |xₖ| ≤ eᵢ`.

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m ν : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `|xᵀΔx| ≤ ∑ₗₖ rₗ wₗₖ rₖ`, rounded up, for `|xₗ| ≤ rₗ` and `0 ≤ Δₗₖ ≤ wₗₖ`. -/
theorem aux_quadMapMatZono_abs_le {x : Vec ℝ n} {Δ : Mat ℝ n n} {r : Vec 𝕋 n} {w : Mat 𝕋 n n}
    (hx : ∀ l, |x l| ≤ toReal (r l)) (hΔ : ∀ l k, 0 ≤ Δ l k ∧ Δ l k ≤ toReal (w l k)) :
    |x ⬝ᵥ (Δ *ᵥ x)| ≤
    toReal (sumUp fun l => sumUp fun k => mulUp (mulUp (r l) (w l k)) (r k)) := by -- --- PROOF ---
  -- one term `|xₗ| Δₗₖ |xₖ|`, under its rounded product
  have hterm : ∀ l k, |x l * (Δ l k * x k)| ≤ toReal (mulUp (mulUp (r l) (w l k)) (r k)) :=
    fun l k => by
      have h1 : |x l| * Δ l k ≤ toReal (mulUp (r l) (w l k)) :=
        (mul_le_mul (hx l) (hΔ l k).2 (hΔ l k).1 ((abs_nonneg _).trans (hx l))).trans
          (mul_le_mulUp _ _)
      have h2 : |x l| * Δ l k * |x k| ≤ toReal (mulUp (mulUp (r l) (w l k)) (r k)) :=
        (mul_le_mul h1 (hx k) (abs_nonneg _)
          ((mul_nonneg (abs_nonneg _) (hΔ l k).1).trans h1)).trans (mul_le_mulUp _ _)
      rw [abs_mul, abs_mul, abs_of_nonneg (hΔ l k).1, ← mul_assoc]
      exact h2
  -- the double sum, each level rounded up
  calc |x ⬝ᵥ (Δ *ᵥ x)| = |∑ l, ∑ k, x l * (Δ l k * x k)| := by
        simp only [dotProduct, mulVec, Finset.mul_sum]
    _ ≤ ∑ l, ∑ k, |x l * (Δ l k * x k)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun l _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ l, toReal (sumUp fun k => mulUp (mulUp (r l) (w l k)) (r k)) :=
        Finset.sum_le_sum fun l _ =>
          (Finset.sum_le_sum fun k _ => hterm l k).trans (sum_le_sumUp _)
    _ ≤ _ := sum_le_sumUp _


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 1], at float zonotopes and interval-matrix centers. -/
theorem Zonotope.quadMapMatZono_outer (D : Fin m → Interval (Mat 𝕋 n n))
    (K : Fin ν → Fin m → Mat 𝕋 n n) (Z : Zonotope (Vec 𝕋 n)) : -- --- STMT ---
    {l : Vec ℝ m | ∃ x ∈ Z.construct, ∃ Dr : Fin m → Mat ℝ n n,
        (∀ i, Dr i ∈ (D i).construct) ∧ ∃ β : Fin ν → ℝ, (∀ j, |β j| ≤ 1) ∧
        ∀ i, l i = x ⬝ᵥ ((Dr i + ∑ j, β j • toRealMat (K j i)) *ᵥ x)}
      ⊆ (Z.quadMapMatZono D K).construct := by -- --- PROOF ---
  rintro l ⟨x, hx, Dr, hDr, β, hβ, hl⟩
  -- the three parts
  set qD : Vec ℝ m := Real.PolyZonotope.quadEval (fun i => toRealMat (D i).inf) x with hqD
  set v : ℕ → Vec ℝ m := fun j => if hj : j < ν then
    β ⟨j, hj⟩ • Real.PolyZonotope.quadEval (fun i => toRealMat (K ⟨j, hj⟩ i)) x else 0 with hv
  set qE : Vec ℝ m := fun i => x ⬝ᵥ ((Dr i - toRealMat (D i).inf) *ᵥ x) with hqE
  have hsplit : l = (qD + ∑ j ∈ Finset.range ν, v j) + qE := by
    funext i
    rw [hl i, Finset.sum_range (fun j => v j)]
    simp only [hqD, hv, hqE, Pi.add_apply, Finset.sum_apply, Fin.is_lt, dif_pos, Fin.eta,
      Pi.smul_apply, smul_eq_mul, Real.PolyZonotope.quadEval, Matrix.add_mulVec,
      Matrix.sub_mulVec, dotProduct_add, dotProduct_sub, Matrix.sum_mulVec, dotProduct_sum,
      Matrix.smul_mulVec, dotProduct_smul]
    ring
  rw [hsplit]
  refine Zonotope.plus_outer _ _ (Set.add_mem_add (Zonotope.plus_outer _ _ (Set.add_mem_add
    (Zonotope.quadMap_outer _ Z ⟨x, hx, rfl⟩) ?_)) ?_)
  · -- `∑ⱼ βⱼ xᵀK⁽ʲ⁾x`, one point of each `[-1, 1] ⊗ Z_K(j)`
    refine Zonotope.sum_mem_sumTerms _ v ν fun j hj => ?_
    simp only [hv, dif_pos hj]
    exact Zonotope.unitIntervalMul_outer _ (hβ ⟨j, hj⟩) (Zonotope.quadMap_outer _ Z ⟨x, hx, rfl⟩)
  · -- `xᵀ(Dᵣ − D̲)x` in the box `[-e, e]`
    refine Interval.zonotope_contains _ fun i => ?_
    have hD := Interval.mem_mat_iff.mp (hDr i)
    have hb := aux_quadMapMatZono_abs_le (x := x) (Δ := Dr i - toRealMat (D i).inf)
      (r := Z.absBoundError) (w := fun l k => subUp ((D i).sup l k) ((D i).inf l k))
      (fun l => Zonotope.abs_le_absBoundError hx l) (fun l k => by
        have hs := sub_le_subUp ((D i).sup l k) ((D i).inf l k)
        simp only [Matrix.sub_apply, toRealMat]
        constructor <;> linarith [(hD l k).1, (hD l k).2])
    show toReal (neg _) ≤ qE i ∧ qE i ≤ toReal _
    rw [toReal_neg]
    exact abs_le.mp hb

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
