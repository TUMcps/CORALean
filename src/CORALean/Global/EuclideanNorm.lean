import CORALean.Global.Tensor
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Positivity

/-!
# The Euclidean norm of a vector

`Vec ℝ n` is `Fin n → ℝ`, and Mathlib's `Pi` instance gives that type the
*supremum* norm, so `‖·‖` on a vector is not the norm an ellipsoid is described
by. `‖·‖₂` is a bare function rather than a second norm instance, so the type
keeps the metric it has and `dist` goes on meaning what it means elsewhere.

`toEuclidean` is the other half of that arrangement: `EuclideanSpace ℝ (Fin n)`
is a different type carrying `‖·‖₂` as its own norm, and a continuous *linear*
equivalence reaches it, so a statement wanting Mathlib's Euclidean API converts
at the point of use instead of being restated there. `norm_toEuclidean` is the
one lemma joining the two norms.

What an ellipsoid needs — Cauchy–Schwarz, homogeneity, the triangle inequality,
and that the closed unit ball is convex and compact — and the finite-sum
triangle inequality a Hausdorff bound asks of it.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   16-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}

noncomputable def norm₂ (x : Vec ℝ n) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- Deliberately not `‖·‖`, which at `Vec ℝ n` is the supremum norm. -/
scoped notation "‖" x "‖₂" => norm₂ x

/-- The same vector in the type whose own norm is `‖·‖₂`. Linear and a
homeomorphism, so sums, images, convexity and compactness all cross it. -/
noncomputable def toEuclidean : Vec ℝ n ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm

@[simp] theorem toEuclidean_apply (x : Vec ℝ n) (i : Fin n) : toEuclidean x i = x i := rfl

/-- What makes the conversion worth anything: `EuclideanSpace.norm_eq` is
`norm₂`'s definition verbatim, so the two norms agree across it. -/
theorem norm_toEuclidean (x : Vec ℝ n) : ‖toEuclidean x‖ = ‖x‖₂ := by
  rw [EuclideanSpace.norm_eq]
  exact congrArg Real.sqrt (Finset.sum_congr rfl fun i _ => by
    rw [toEuclidean_apply, Real.norm_eq_abs, sq_abs])


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_sum_sq_nonneg (x : Vec ℝ n) : 0 ≤ ∑ i, x i ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem norm₂_nonneg (x : Vec ℝ n) : 0 ≤ ‖x‖₂ := Real.sqrt_nonneg _

theorem norm₂_sq (x : Vec ℝ n) : ‖x‖₂ ^ 2 = ∑ i, x i ^ 2 :=
  Real.sq_sqrt (aux_sum_sq_nonneg x)

theorem dotProduct_self (x : Vec ℝ n) : x ⬝ᵥ x = ‖x‖₂ ^ 2 := by
  rw [norm₂_sq]
  exact Finset.sum_congr rfl fun i _ => (sq (x i)).symm

theorem norm₂_zero : ‖(0 : Vec ℝ n)‖₂ = 0 := by
  rw [← norm_toEuclidean, map_zero, norm_zero]

theorem norm₂_smul (r : ℝ) (x : Vec ℝ n) : ‖r • x‖₂ = |r| * ‖x‖₂ := by
  rw [← norm_toEuclidean, ← norm_toEuclidean x, map_smul, norm_smul, Real.norm_eq_abs]

/-- Cauchy–Schwarz in magnitude. The two-sided form is what a box conversion
needs, a coordinate reaching as far in one direction as in the other. -/
theorem abs_dotProduct_le_norm₂_mul_norm₂ (x y : Vec ℝ n) :
    |x ⬝ᵥ y| ≤ ‖x‖₂ * ‖y‖₂ := by -- --- PROOF ---
  have hcs : (∑ i, x i * y i) ^ 2 ≤ (∑ i, x i ^ 2) * ∑ i, y i ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  calc |x ⬝ᵥ y| = Real.sqrt ((∑ i, x i * y i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i, x i ^ 2) * ∑ i, y i ^ 2) := Real.sqrt_le_sqrt hcs
    _ = ‖x‖₂ * ‖y‖₂ := Real.sqrt_mul (aux_sum_sq_nonneg x) _

/-- Cauchy–Schwarz, which is the whole of the ellipsoid's support function. -/
theorem dotProduct_le_norm₂_mul_norm₂ (x y : Vec ℝ n) : x ⬝ᵥ y ≤ ‖x‖₂ * ‖y‖₂ :=
  le_trans (le_abs_self _) (abs_dotProduct_le_norm₂_mul_norm₂ x y)

/-- The triangle inequality over a finite sum, which is `norm_sum_le` pulled
back through the equivalence rather than an induction of its own. -/
theorem norm₂_sum_le {ι : Type} (s : Finset ι) (f : ι → Vec ℝ n) :
    ‖∑ j ∈ s, f j‖₂ ≤ ∑ j ∈ s, ‖f j‖₂ := by
  rw [← norm_toEuclidean, map_sum]
  refine (norm_sum_le s _).trans_eq (Finset.sum_congr rfl fun j _ => ?_)
  exact norm_toEuclidean (f j)

theorem norm₂_add_le (x y : Vec ℝ n) : ‖x + y‖₂ ≤ ‖x‖₂ + ‖y‖₂ := by
  rw [← norm_toEuclidean, ← norm_toEuclidean x, ← norm_toEuclidean y, map_add]
  exact norm_add_le _ _

/-- One coordinate never exceeds the whole, which is `PiLp.norm_apply_le` read
back through the equivalence. -/
theorem abs_le_norm₂ (x : Vec ℝ n) (i : Fin n) : |x i| ≤ ‖x‖₂ := by
  rw [← norm_toEuclidean, ← Real.norm_eq_abs, ← toEuclidean_apply x i]
  exact PiLp.norm_apply_le _ _

/-- And the whole never exceeds `√n` coordinates, which is what converts a bound
at the ambient supremum norm into one at `‖·‖₂`. -/
theorem norm₂_le_sqrt_mul_norm (x : Vec ℝ n) : ‖x‖₂ ≤ Real.sqrt n * ‖x‖ := by -- --- PROOF ---
  have hle : ∀ i : Fin n, x i ^ 2 ≤ ‖x‖ ^ 2 := fun i =>
    calc x i ^ 2 = |x i| ^ 2 := (sq_abs _).symm
      _ ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _)
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i) 2
  have hsum : ∑ i, x i ^ 2 ≤ (n : ℝ) * ‖x‖ ^ 2 := by
    calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin n, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => hle i
      _ = (n : ℝ) * ‖x‖ ^ 2 := by simp
  calc ‖x‖₂ = Real.sqrt (∑ i, x i ^ 2) := rfl
    _ ≤ Real.sqrt ((n : ℝ) * ‖x‖ ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt n * ‖x‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (norm_nonneg _)]

/-- The closed unit ball, which is what an ellipsoid is the affine image of. -/
def unitBall₂ (n : ℕ) : Set (Vec ℝ n) := {x | ‖x‖₂ ≤ 1}

theorem mem_unitBall₂ {x : Vec ℝ n} : x ∈ unitBall₂ n ↔ ‖x‖₂ ≤ 1 := Iff.rfl

theorem zero_mem_unitBall₂ : (0 : Vec ℝ n) ∈ unitBall₂ n := by
  rw [mem_unitBall₂, norm₂_zero]
  exact zero_le_one

theorem continuous_norm₂ : Continuous (norm₂ : Vec ℝ n → ℝ) :=
  Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2)

/-- The unit ball is the closed unit ball of `EuclideanSpace ℝ (Fin n)`, read
back through the equivalence. -/
theorem unitBall₂_eq_image :
    unitBall₂ n = toEuclidean.symm '' Metric.closedBall 0 1 := by
  rw [ContinuousLinearEquiv.image_symm_eq_preimage]
  ext x
  rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, norm_toEuclidean]
  exact Iff.rfl

theorem convex_unitBall₂ : Convex ℝ (unitBall₂ n) := by
  rw [unitBall₂_eq_image]
  exact (convex_closedBall _ _).linear_image toEuclidean.symm.toLinearEquiv.toLinearMap


-- =======================================  MAIN THEOREM  ======================================= --

/-- The continuous image of a closed ball that is compact where it is stated,
`EuclideanSpace ℝ (Fin n)` being finite-dimensional. -/
theorem isCompact_unitBall₂ : IsCompact (unitBall₂ n) := by
  rw [unitBall₂_eq_image]
  exact (isCompact_closedBall _ _).image toEuclidean.symm.continuous

/-- The Euclidean norm never exceeds the sum of magnitudes: the square of the latter has every
cross term the former drops, all of them nonnegative. -/
theorem norm₂_le_sum_abs (x : Vec ℝ n) : ‖x‖₂ ≤ ∑ i, |x i| := by -- --- PROOF ---
  have hsq : ∑ i, x i ^ 2 ≤ (∑ i, |x i|) ^ 2 := by
    have hi : ∀ i, x i ^ 2 ≤ |x i| * ∑ j, |x j| := fun i => by
      rw [← sq_abs (x i), sq]
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)) (abs_nonneg _)
    calc ∑ i, x i ^ 2 ≤ ∑ i, |x i| * ∑ j, |x j| := Finset.sum_le_sum fun i _ => hi i
      _ = (∑ i, |x i|) * ∑ j, |x j| := (Finset.sum_mul _ _ _).symm
      _ = (∑ i, |x i|) ^ 2 := (sq _).symm
  exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq (by positivity))

/-- Applying a matrix scales the Euclidean norm by at most the sum of its rows' own: each row's
dot product with `x` is Cauchy–Schwarz-bounded, and the Euclidean norm is under the row sum. -/
theorem norm₂_mulVec_le (M : Mat ℝ n n) (x : Vec ℝ n) :
    ‖M.mulVec x‖₂ ≤ (∑ i, ‖(fun j => M i j)‖₂) * ‖x‖₂ := by -- --- PROOF ---
  have hrow : ∀ i, |M.mulVec x i| ≤ ‖(fun j => M i j)‖₂ * ‖x‖₂ :=
    fun i => abs_dotProduct_le_norm₂_mul_norm₂ (fun j => M i j) x
  calc ‖M.mulVec x‖₂ ≤ ∑ i, |M.mulVec x i| := norm₂_le_sum_abs _
    _ ≤ ∑ i, ‖(fun j => M i j)‖₂ * ‖x‖₂ := Finset.sum_le_sum fun i _ => hrow i
    _ = (∑ i, ‖(fun j => M i j)‖₂) * ‖x‖₂ := (Finset.sum_mul _ _ _).symm

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
