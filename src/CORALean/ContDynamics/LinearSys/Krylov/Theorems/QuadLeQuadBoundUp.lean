module

public import CORALean.ContDynamics.LinearSys.Krylov.Operations.QuadBoundUp
public import CORALean.Global.Float.SoundFloatArithmetic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The quadratic form of a matrix is below Gershgorin's bound

For a real matrix `B` and `x`, `x*Bx = Σ_{i,j} B_{ij} x_i x_j ≤ Σ_i B_{ii} x_i² + Σ_{i≠j}
|B_{ij}|(x_i² + x_j²)/2 = Σ_i x_i² (B_{ii} + ½ Σ_{j≠i} (|B_{ij}| + |B_{ji}|))`, so `x*Bx ≤ μ x*x`
for every `μ` above the row bounds, the hypothesis `W(σA) ⊆ ℂ⁻` of [1, Thm. 1] with a growth rate;
`Krylov.quadBoundUp` is such a `μ`, rounded up.

## Inputs
* `M` – float matrix
* `x` – real vector

## Hypotheses
* none

## Conclusion
* the quadratic form is at most the bound times the squared length

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov approximations
      to matrix exponentials and associated φ-functions". BIT Numerical Mathematics,
      2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {k : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The row sums of Gershgorin's discs bound the quadratic form of a real matrix. -/
private theorem aux_quad_le (B : Mat ℝ k k) (x : Vec ℝ k) : -- --- CONCL ---
    x ⬝ᵥ (B *ᵥ x) ≤
      ∑ i, x i ^ 2 *
        (B i i + (∑ j, if j = i then 0 else |B i j| + |B j i|) / 2) := by -- --- PROOF ---
  set o : Fin k → Fin k → ℝ := fun i j => if j = i then 0 else |B i j| with ho
  have hpt : ∀ i j, B i j * x i * x j ≤
      (if i = j then B i i * x i ^ 2 else 0) + (o i j * x i ^ 2 + o i j * x j ^ 2) / 2 := by
    -- each entry against its share of the discs
    intro i j
    by_cases h : i = j
    · subst h; simp [ho, sq, mul_assoc]
    · have hj : j ≠ i := fun e => h e.symm
      simp only [ho, h, hj, if_false, zero_add]
      have h1 : B i j * x i * x j ≤ |B i j| * |x i| * |x j| := by
        calc B i j * x i * x j ≤ |B i j * x i * x j| := le_abs_self _
          _ = |B i j| * |x i| * |x j| := by rw [abs_mul, abs_mul]
      have h2 : |x i| * |x j| ≤ (x i ^ 2 + x j ^ 2) / 2 := by
        nlinarith [sq_abs (x i), sq_abs (x j), sq_nonneg (|x i| - |x j|)]
      calc B i j * x i * x j ≤ |B i j| * (|x i| * |x j|) := by linarith
        _ ≤ |B i j| * ((x i ^ 2 + x j ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = _ := by ring
  have hcomm : ∑ i, ∑ j, o i j * x j ^ 2 = ∑ i, ∑ j, o j i * x i ^ 2 :=
    Finset.sum_comm (f := fun i j => o i j * x j ^ 2)
  -- the quadratic form as the double sum of the entries
  calc x ⬝ᵥ (B *ᵥ x) = ∑ i, ∑ j, B i j * x i * x j := by
        simp only [dotProduct, mulVec, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ i, ∑ j, ((if i = j then B i i * x i ^ 2 else 0) +
        (o i j * x i ^ 2 + o i j * x j ^ 2) / 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
    _ = ∑ i, B i i * x i ^ 2 + (∑ i, ∑ j, o i j * x i ^ 2 + ∑ i, ∑ j, o j i * x i ^ 2) * 2⁻¹ := by
        -- the shares summed, the off-diagonal part symmetrized
        rw [← hcomm]
        simp only [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.sum_mul, add_mul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = ∑ i, x i ^ 2 * (B i i + (∑ j, if j = i then 0 else |B i j| + |B j i|) / 2) := by
        have h1 : ∀ i, x i ^ 2 * (B i i + (∑ j, if j = i then 0 else |B i j| + |B j i|) / 2) =
            B i i * x i ^ 2 + (∑ j, (o i j * x i ^ 2 + o j i * x i ^ 2)) * 2⁻¹ := by
          intro i
          have : (∑ j, if j = i then (0 : ℝ) else |B i j| + |B j i|) =
              ∑ j, (o i j + o j i) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases h : j = i
            · simp [ho, h]
            · simp [ho, h, Ne.symm h]
          rw [this, div_eq_mul_inv]
          simp only [← add_mul, ← Finset.sum_mul]
          ring
        simp only [h1, Finset.sum_add_distrib, ← Finset.sum_mul]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Krylov.quad_le_quadBoundUp (M : Mat 𝕋 k k) (x : Vec ℝ k) : -- --- CONCL ---
    x ⬝ᵥ (toRealMat M *ᵥ x) ≤ toReal (Krylov.quadBoundUp M) * (x ⬝ᵥ x) := by -- --- PROOF ---
  refine (aux_quad_le (toRealMat M) x).trans ?_
  rw [dotProduct, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  -- the row bound is below the float one
  have hr : toRealMat M i i + (∑ j, if j = i then 0 else
      |toRealMat M i j| + |toRealMat M j i|) / 2 ≤ toReal (Krylov.quadBoundUp M) := by
    refine le_trans ?_ (le_maximumOver _ i)
    refine le_trans ?_ (add_le_addUp _ _)
    rw [toReal_half]
    -- the float sum covers the real one
    have hs : (∑ j, if j = i then 0 else |toRealMat M i j| + |toRealMat M j i|) ≤
        toReal (sumUp fun j => if j = i then (zero : 𝕋) else
          addUp (absolute (M i j)) (absolute (M j i))) := by
      refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
      by_cases h : j = i
      · simp [h, toReal_zero]
      · simp only [h, if_false]
        refine le_trans ?_ (add_le_addUp _ _)
        rw [toReal_absolute, toReal_absolute]
        exact le_rfl
    show toReal (M i i) + _ ≤ toReal (M i i) + _
    linarith
  nlinarith [sq_nonneg (x i)]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
