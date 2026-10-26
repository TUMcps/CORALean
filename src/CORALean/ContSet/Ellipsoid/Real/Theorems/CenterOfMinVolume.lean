module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemOfShapeIff
public import CORALean.ContSet.Ellipsoid.Real.Theorems.OfShapeEq
public import CORALean.ContSet.Ellipsoid.Real.Operations.OfShape
public import CORALean.ContSet.Ellipsoid.Real.Operations.Volume
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A minimum volume outer ellipsoid of a sum of ellipsoids is centered at the sum of the centers

[1, Eq. 8]: the sum `E(q₁, Q₁) ⊕ ⋯ ⊕ E(q_K, Q_K)` is symmetric about `c = q₁ + ⋯ + q_K`, so an
enclosing `E(q, Q)` also encloses its mirror image in `c`, hence the intersection, which lies in
the ellipsoid `{(x - c)ᵀ Q⁻¹ (x - c) ≤ 1 - (q - c)ᵀ Q⁻¹ (q - c)}` centered at `c`. Unless `q = c`
that is a strictly smaller volume. Existence and uniqueness of the minimum are not used.

## Inputs
* `K` – number of ellipsoids
* `Qs` – shape matrices
* `qs` – centers
* `Q` – shape of the outer ellipsoid
* `q` – center of the outer ellipsoid

## Hypotheses
* `hQs` – each `Qs k` positive definite
* `hQ` – `Q` positive definite
* `hsub` – the sum lies in the outer ellipsoid
* `hmin` – the outer ellipsoid has minimum volume

## Conclusion
* the center `q` is the sum of the centers

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of Minkowski
      sum of ellipsoids". 2018 IEEE Conference on Decision and Control (CDC), 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise
open scoped MatrixOrder

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The sum is symmetric about the sum of the centers. -/
private theorem aux_sum_reflect {K : ℕ} (Qs : Fin K → Mat ℝ n n) (qs : Fin K → Vec ℝ n)
    (hQs : ∀ k, (Qs k).PosDef) {x : Vec ℝ n}
    (hx : x ∈ ∑ k, (Ellipsoid.ofShape (Qs k) (qs k)).construct) : -- --- CONCL ---
    (2 : ℝ) • ∑ k, qs k - x
      ∈ ∑ k, (Ellipsoid.ofShape (Qs k) (qs k)).construct := by -- --- PROOF ---
  rw [Set.mem_finsetSum] at hx ⊢
  obtain ⟨g, hg, rfl⟩ := hx
  refine ⟨fun k => (2 : ℝ) • qs k - g k, fun {k} hk => ?_, ?_⟩
  · -- the mirror image of a point of an ellipsoid is a point of it
    have h := (Ellipsoid.mem_ofShape_iff (hQs k) (qs k) (g k)).1 (hg hk)
    refine (Ellipsoid.mem_ofShape_iff (hQs k) (qs k) _).2 ?_
    have e : (2 : ℝ) • qs k - g k - qs k = -(g k - qs k) := by
      ext i; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring
    rw [e, neg_dotProduct, Matrix.mulVec_neg, dotProduct_neg, neg_neg]
    exact h
  · simp only [Finset.sum_sub_distrib, ← Finset.smul_sum]

/-- The quadratic form is subadditive on the mirrored pair. -/
private theorem aux_quad_parallelogram (A : Mat ℝ n n) (y p : Vec ℝ n) :
    (y - p) ⬝ᵥ A *ᵥ (y - p) + (y + p) ⬝ᵥ A *ᵥ (y + p)
      = 2 * (y ⬝ᵥ A *ᵥ y) + 2 * (p ⬝ᵥ A *ᵥ p) := by
  simp only [Matrix.mulVec_sub, Matrix.mulVec_add, sub_dotProduct, dotProduct_sub, add_dotProduct,
    dotProduct_add]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Eq. 8]: a minimum volume outer ellipsoid of `E(q₁, Q₁) ⊕ ⋯ ⊕ E(q_K, Q_K)` has center
`q₁ + ⋯ + q_K`. -/
theorem Ellipsoid.center_of_min_volume {K : ℕ} (Qs : Fin K → Mat ℝ n n) (qs : Fin K → Vec ℝ n)
    (hQs : ∀ k, (Qs k).PosDef) {Q : Mat ℝ n n} (q : Vec ℝ n) (hQ : Q.PosDef)
    (hsub : ∑ k, (Ellipsoid.ofShape (Qs k) (qs k)).construct ⊆ (Ellipsoid.ofShape Q q).construct)
    (hmin : ∀ (Q' : Mat ℝ n n) (q' : Vec ℝ n), Q'.PosDef →
      ∑ k, (Ellipsoid.ofShape (Qs k) (qs k)).construct ⊆ (Ellipsoid.ofShape Q' q').construct →
        (Ellipsoid.ofShape Q q).volume ≤ (Ellipsoid.ofShape Q' q').volume) : -- --- CONCL ---
    q = ∑ k, qs k := by -- --- PROOF ---
  by_contra hne
  set c : Vec ℝ n := ∑ k, qs k with hc
  set A : Mat ℝ n n := Q⁻¹ with hA
  set p : Vec ℝ n := q - c with hp
  have hp0 : p ≠ 0 := fun h => hne (sub_eq_zero.1 h)
  have hAp : 0 < p ⬝ᵥ A *ᵥ p := by
    simpa using hQ.inv.dotProduct_mulVec_pos hp0
  -- the points of the sum satisfy the averaged inequality
  have hmem : ∀ x ∈ ∑ k, (Ellipsoid.ofShape (Qs k) (qs k)).construct,
      (x - c) ⬝ᵥ A *ᵥ (x - c) ≤ 1 - p ⬝ᵥ A *ᵥ p := by
    intro x hx
    have h1 := (Ellipsoid.mem_ofShape_iff hQ q x).1 (hsub hx)
    have h2 := (Ellipsoid.mem_ofShape_iff hQ q _).1
      (hsub (aux_sum_reflect Qs qs hQs hx))
    have e1 : x - q = (x - c) - p := by rw [hp]; abel
    have e2 : (2 : ℝ) • c - x - q = -((x - c) + p) := by
      rw [hp]; ext i; simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.add_apply,
        smul_eq_mul]; ring
    rw [e1] at h1
    rw [e2, neg_dotProduct, Matrix.mulVec_neg, dotProduct_neg, neg_neg] at h2
    have := aux_quad_parallelogram A (x - c) p
    linarith
  -- the center itself is in the sum, so the form is at most one
  have hcmem : c ∈ ∑ k, (Ellipsoid.ofShape (Qs k) (qs k)).construct := by
    rw [Set.mem_finsetSum]
    refine ⟨qs, fun {k} _ => (Ellipsoid.mem_ofShape_iff (hQs k) (qs k) _).2 ?_, rfl⟩
    simp
  -- at the center the form vanishes, so the form of `p` is at most one
  have hle := hmem c hcmem
  simp only [sub_self, Matrix.mulVec_zero, dotProduct_zero] at hle
  -- the shrunk ellipsoid at `c` still contains the sum and has less volume
  set a : ℝ := p ⬝ᵥ A *ᵥ p with ha
  set t : ℝ := 1 - a / 2 with ht
  have ht0 : 0 < t := by linarith
  have ht1 : t < 1 := by linarith
  -- the shrunk shape `t Q` is positive definite
  have hQ' : (t • Q).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · unfold IsHermitian
      rw [conjTranspose_eq_transpose_of_trivial, transpose_smul]
      exact congrArg (t • ·) (by simpa [conjTranspose_eq_transpose_of_trivial] using hQ.1.eq)
    · simp only [star_trivial, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      exact mul_pos ht0 (by simpa using hQ.dotProduct_mulVec_pos hx)
  have hcont : ∑ k, (Ellipsoid.ofShape (Qs k) (qs k)).construct
      ⊆ (Ellipsoid.ofShape (t • Q) c).construct := by
    intro x hx
    refine (Ellipsoid.mem_ofShape_iff hQ' c x).2 ?_
    have hu : IsUnit Q.det := (isUnit_iff_isUnit_det Q).1 hQ.isUnit
    have hinv : (t • Q)⁻¹ = t⁻¹ • Q⁻¹ := Matrix.inv_eq_left_inv (by
      rw [smul_mul_assoc, mul_smul_comm, Matrix.nonsing_inv_mul Q hu, smul_smul,
        inv_mul_cancel₀ ht0.ne', one_smul])
    rw [hinv, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← hA, inv_mul_le_iff₀ ht0]
    have := hmem x hx
    linarith
  have hvol := hmin (t • Q) c hQ' hcont
  -- `n = 0` is excluded by `p ≠ 0`, and the volume ratio is `t ^ n < 1`
  have hn : n ≠ 0 := by
    rintro rfl
    exact hp0 (Subsingleton.elim _ _)
  simp only [Ellipsoid.volume, Ellipsoid.ofShape_eq hQ.posSemidef,
    Ellipsoid.ofShape_eq hQ'.posSemidef, Matrix.det_smul, Fintype.card_fin] at hvol
  -- the unit ball volume and `det Q` are positive
  have hV : 0 < Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1) :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  have hd : 0 < Q.det := hQ.det_pos
  have htn : t ^ n < 1 := pow_lt_one₀ ht0.le ht1 hn
  -- cancel the common factors in `V √det`
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hvol
  have h1 := le_of_mul_le_mul_left hvol hV
  rw [Real.sqrt_le_sqrt_iff (by positivity)] at h1
  nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
