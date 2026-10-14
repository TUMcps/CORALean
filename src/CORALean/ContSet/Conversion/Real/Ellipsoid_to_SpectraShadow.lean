module

public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# An ellipsoid as a spectrahedral shadow

Exact. In the generator form `x = q + G u`, `‖u‖₂ ≤ 1`, the unit ball is the inequality
`[[1, uᵀ], [u, I]] ⪰ 0`, written `I + Σᵢ uᵢ Aᵢ ⪰ 0` with `Aᵢ = e₀eᵢ₊₁ᵀ + eᵢ₊₁e₀ᵀ`, and the
centre and generators are the ellipsoid's own. Its quadratic form is `a² + 2a (u·y) + ‖y‖²`, which
is nonnegative everywhere iff `‖u‖₂ ≤ 1`. This is not CORA's matrices: CORA's `spectraShadow`
writes the set as `{x | 1 - (x-q)ᵀ Q⁻¹ (x-q) ≥ 0}` from `chol(inv(Q))`, and by an SVD when `Q` is
singular, and has no generators; the generator form needs neither, and no degenerate split.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean Matrix

variable {n : ℕ}

/-- The ellipsoid as the shadow of `‖u‖₂ ≤ 1`, the ball written as one linear matrix
inequality of size `k + 1`. -/
def Ellipsoid.spectraShadow (E : Ellipsoid n) : SpectraShadow (Vec ℝ n) where
  k := E.k + 1
  m := E.k
  A₀ := 1
  A := fun i => Matrix.of fun p q =>
    if (p = 0 ∧ q = i.succ) ∨ (p = i.succ ∧ q = 0) then 1 else 0
  c := E.c
  G := fun i r => E.G r i


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The inequality's matrix is symmetric. -/
theorem Ellipsoid.aux_lmi_isHermitian {k : ℕ} (u : Fin k → ℝ) :
    ((1 : Mat ℝ (k + 1) (k + 1)) + ∑ i, u i • (Matrix.of fun p q : Fin (k + 1) =>
      if (p = 0 ∧ q = i.succ) ∨ (p = i.succ ∧ q = 0) then (1 : ℝ) else 0)).IsHermitian
    := by -- --- PROOF ---
  -- symmetric entry by entry: the identity is, and each `Aᵢ` swaps its two cases
  refine Matrix.IsHermitian.ext fun p q => ?_
  simp only [star_trivial, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, Matrix.one_apply]
  congr 1
  · simp [eq_comm]
  · exact Finset.sum_congr rfl fun i _ => by simp only [or_comm, and_comm]

/-- One `Aᵢ` has the quadratic form `2 x₀ xᵢ₊₁`. -/
theorem Ellipsoid.aux_A_form {k : ℕ} (i : Fin k) (x : Fin (k + 1) → ℝ) :
    x ⬝ᵥ ((Matrix.of fun p q : Fin (k + 1) =>
      if (p = 0 ∧ q = i.succ) ∨ (p = i.succ ∧ q = 0) then (1 : ℝ) else 0) *ᵥ x) =
      2 * x 0 * x i.succ := by -- --- PROOF ---
  have h0 : (0 : Fin (k + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  unfold dotProduct Matrix.mulVec dotProduct
  rw [Fintype.sum_eq_add 0 i.succ h0 (fun p hp => by simp [hp.1, hp.2])]
  simp [h0, h0.symm, Finset.sum_ite_eq']
  ring

/-- The inequality's quadratic form: `a² + 2a (u·y) + ‖y‖²` at `x = (a, y)`. -/
theorem Ellipsoid.aux_lmi_form {k : ℕ} (u : Fin k → ℝ) (x : Fin (k + 1) → ℝ) :
    x ⬝ᵥ (((1 : Mat ℝ (k + 1) (k + 1)) + ∑ i, u i • (Matrix.of fun p q : Fin (k + 1) =>
      if (p = 0 ∧ q = i.succ) ∨ (p = i.succ ∧ q = 0) then (1 : ℝ) else 0)) *ᵥ x) =
      x 0 ^ 2 + 2 * x 0 * ∑ i : Fin k, u i * x i.succ + ∑ i : Fin k, x i.succ ^ 2
    := by -- --- PROOF ---
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_sum, dotProduct_smul, Ellipsoid.aux_A_form]
  simp only [dotProduct, Fin.sum_univ_succ, smul_eq_mul, Finset.mul_sum, sq]
  have e : ∑ j : Fin k, u j * (2 * x 0 * x j.succ) = ∑ j : Fin k, 2 * x 0 * (u j * x j.succ) :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [e]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.posSemidef_spectraShadow_iff (E : Ellipsoid n) (u : Vec ℝ E.k) :
    (E.spectraShadow.A₀ + ∑ i, u i • E.spectraShadow.A i).PosSemidef ↔ ‖u‖₂ ≤ 1
    := by -- --- PROOF ---
  change ((1 : Mat ℝ (E.k + 1) (E.k + 1)) + ∑ i, u i • (Matrix.of fun p q : Fin (E.k + 1) =>
    if (p = 0 ∧ q = i.succ) ∨ (p = i.succ ∧ q = 0) then (1 : ℝ) else 0)).PosSemidef ↔ _
  constructor
  · intro h
    -- the point `(-1, u)` has quadratic form `1 - ‖u‖²`
    by_contra hu
    push Not at hu
    have hq := h.dotProduct_mulVec_nonneg (Fin.cons (-1) u)
    simp only [star_trivial, Ellipsoid.aux_lmi_form, Fin.cons_zero, Fin.cons_succ] at hq
    have hs : ∑ i, u i * u i = ‖u‖₂ ^ 2 := by rw [norm₂_sq]; simp [sq]
    have hs2 : ∑ i, u i ^ 2 = ‖u‖₂ ^ 2 := (norm₂_sq u).symm
    rw [hs, hs2] at hq
    nlinarith
  · intro hu
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Ellipsoid.aux_lmi_isHermitian u)
      fun x => ?_
    rw [star_trivial, Ellipsoid.aux_lmi_form]
    have hv := abs_dotProduct_le_norm₂_mul_norm₂ u (fun i => x i.succ)
    have hy : ‖fun i => x i.succ‖₂ ^ 2 = ∑ i : Fin E.k, x i.succ ^ 2 := norm₂_sq _
    have hv2 : (∑ i, u i * x i.succ) ^ 2 ≤ ∑ i : Fin E.k, x i.succ ^ 2 := by
      rw [← hy, ← sq_abs]
      have := mul_le_mul_of_nonneg_right hu (norm₂_nonneg (fun i => x i.succ))
      exact pow_le_pow_left₀ (abs_nonneg _) (hv.trans (by linarith)) 2
    nlinarith [sq_nonneg (x 0 + ∑ i, u i * x i.succ)]

theorem Ellipsoid.spectraShadow_exact (E : Ellipsoid n) :
    E.construct = E.spectraShadow.construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨u, (Ellipsoid.posSemidef_spectraShadow_iff E u).mpr hu, ?_⟩
    funext r
    simp only [Ellipsoid.spectraShadow, Matrix.mulVec, dotProduct, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact congrArg _ (Finset.sum_congr rfl fun _ _ => mul_comm _ _)
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨u, (Ellipsoid.posSemidef_spectraShadow_iff E u).mp hu, ?_⟩
    funext r
    simp only [Ellipsoid.spectraShadow, Matrix.mulVec, dotProduct, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact congrArg _ (Finset.sum_congr rfl fun _ _ => mul_comm _ _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
