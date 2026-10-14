module

public import CORALean.ContSet.Ellipsoid.Real.Operations.IntersectStripGollamudi
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemOfShapeIff
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The corrected Gollamudi update encloses the intersection

For positive-definite `Q` and `λ ∈ [0, 1)`, every point `x` of the ellipsoid `E(Q, c)` with
`‖C x - y‖₂ ≤ φ` lies in `intersectStripGollamudi Q c C φ y λ`. With `T = (1 - λ) I + λ C Q Cᵀ`,
`w = T⁻¹ δ`, `u = Cᵀ w` and `invQ = (1 - λ) Q⁻¹ + λ Cᵀ C`, one has `invQ Q Cᵀ = Cᵀ T`, so the
centre is `c* = c + λ Q u`, `C c* - y = -(1 - λ) w`, and with `d = x - c*`

  `(1 - λ)(x - c)ᵀ Q⁻¹ (x - c) + λ ‖C x - y‖₂² = dᵀ invQ d + λ (1 - λ) δᵀ w`,

the cross terms `2 λ (1 - λ) dᵀ u` cancelling. The left side is at most `1 - λ + λ φ²`, so
`dᵀ invQ d ≤ σ²`, which is membership in the ellipsoid of shape `σ² invQ⁻¹`; when `σ² = 0` it
forces `d = 0`, the centre. CORA divides by `σ²` instead
(`intersectStripGollamudi1D_counterexample`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A real positive-definite matrix is symmetric. -/
theorem Ellipsoid.aux_transpose_eq {A : Mat ℝ n n} (hA : A.PosDef) : Aᵀ = A := by
  have h := hA.isHermitian.eq
  simpa [conjTranspose_eq_transpose_of_trivial] using h

/-- The quadratic form of a symmetric matrix is symmetric in its two arguments. -/
theorem Ellipsoid.aux_dot_symm {A : Mat ℝ n n} (hA : Aᵀ = A) (u v : Vec ℝ n) :
    u ⬝ᵥ A *ᵥ v = v ⬝ᵥ A *ᵥ u := by
  rw [← Ellipsoid.dot_transpose, hA, dotProduct_comm]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.intersectStripGollamudi_outer {Q : Mat ℝ n n} (hQ : Q.PosDef) (c : Vec ℝ n)
    (C : Mat ℝ m n) (φ : ℝ) (y : Vec ℝ m) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1) :
    (Ellipsoid.ofShape Q c).construct ∩ {x | ‖C *ᵥ x - y‖₂ ≤ φ}
      ⊆ (Ellipsoid.intersectStripGollamudi Q c C φ y lam).construct := by -- --- PROOF ---
  rintro x ⟨hxE, hxS⟩
  rw [Ellipsoid.mem_ofShape_iff hQ] at hxE
  have hl : 0 < 1 - lam := by linarith
  -- the code's `delta`, `Q_tmp` and `invQ`
  set δ := y - C *ᵥ c with hδ
  set T : Mat ℝ m m := (1 - lam) • (1 : Mat ℝ m m) + lam • (C * Q * Cᵀ) with hT
  set P : Mat ℝ n n := (1 - lam) • Q⁻¹ + lam • (Cᵀ * C) with hP
  -- both are positive definite, so invertible
  have hTpd : T.PosDef := by
    have h := hQ.posSemidef.mul_mul_conjTranspose_same C
    rw [conjTranspose_eq_transpose_of_trivial] at h
    exact (PosDef.one.smul hl).add_posSemidef (h.smul h0)
  have hPpd : P.PosDef := by
    have h := posSemidef_conjTranspose_mul_self C
    rw [conjTranspose_eq_transpose_of_trivial] at h
    exact (hQ.inv.smul hl).add_posSemidef (h.smul h0)
  have hQu : IsUnit Q.det := (isUnit_iff_isUnit_det Q).1 hQ.isUnit
  have hTu : IsUnit T.det := (isUnit_iff_isUnit_det T).1 hTpd.isUnit
  have hPu : IsUnit P.det := (isUnit_iff_isUnit_det P).1 hPpd.isUnit
  have hQiT : Q⁻¹ᵀ = Q⁻¹ := Ellipsoid.aux_transpose_eq hQ.inv
  -- `w = T⁻¹ δ` and `u = Cᵀ w`
  set w := T⁻¹ *ᵥ δ with hw
  have hTw : T *ᵥ w = δ := by rw [hw, mulVec_mulVec, mul_nonsing_inv T hTu, one_mulVec]
  clear_value w
  obtain ⟨u, hu⟩ : ∃ u, u = Cᵀ *ᵥ w := ⟨_, rfl⟩
  have hδu : δ = (1 - lam) • w + lam • (C *ᵥ (Q *ᵥ u)) := by
    rw [← hTw, hT, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hu, mulVec_mulVec,
      mulVec_mulVec]
  -- `invQ Q Cᵀ = Cᵀ T`, so the centre is `c + λ Q u`
  have hM : P * Q * Cᵀ = Cᵀ * T := by
    simp only [hP, hT, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_one, ← Matrix.mul_assoc, nonsing_inv_mul Q hQu, Matrix.one_mul]
  have hcen : P⁻¹ *ᵥ (Cᵀ *ᵥ δ) = Q *ᵥ u := by
    have hPv : P *ᵥ (Q *ᵥ u) = Cᵀ *ᵥ δ := by
      rw [hu, mulVec_mulVec, mulVec_mulVec, hM, ← mulVec_mulVec, hTw]
    rw [← hPv, mulVec_mulVec, nonsing_inv_mul P hPu, one_mulVec]
  -- the goal, at the centre `c + λ Q u`
  show x ∈ (Ellipsoid.ofShape
    ((1 - lam + lam * φ ^ 2 - lam * (1 - lam) * (δ ⬝ᵥ T⁻¹ *ᵥ δ)) • P⁻¹)
      (c + lam • (P⁻¹ *ᵥ (Cᵀ *ᵥ δ)))).construct
  rw [hcen, ← hw]
  set σsq := 1 - lam + lam * φ ^ 2 - lam * (1 - lam) * (δ ⬝ᵥ w) with hσ
  obtain ⟨d, hd⟩ : ∃ d, d = x - (c + lam • (Q *ᵥ u)) := ⟨_, rfl⟩
  -- the scalar pieces: `Q⁻¹ (λ Q u) = λ u`, and `(C a)ᵀ w = aᵀ u`
  have hQie : Q⁻¹ *ᵥ (lam • (Q *ᵥ u)) = lam • u := by
    rw [mulVec_smul, mulVec_mulVec, nonsing_inv_mul Q hQu, one_mulVec]
  have hCa : ∀ a, (C *ᵥ a) ⬝ᵥ w = a ⬝ᵥ u := fun a => by
    rw [hu, dotProduct_comm, ← Ellipsoid.dot_transpose, dotProduct_comm]
  set s := (Q *ᵥ u) ⬝ᵥ u with hs
  -- `δᵀ w = (1 - λ) wᵀ w + λ s`
  have h4 : δ ⬝ᵥ w = (1 - lam) * (w ⬝ᵥ w) + lam * s := by
    conv_lhs => rw [hδu]
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, hCa, smul_eq_mul, smul_eq_mul]
  -- the ellipsoid term: `x - c = d + λ Q u`
  have h1 : (x - c) ⬝ᵥ Q⁻¹ *ᵥ (x - c)
      = d ⬝ᵥ Q⁻¹ *ᵥ d + 2 * lam * (d ⬝ᵥ u) + lam ^ 2 * s := by
    have hx : x - c = d + lam • (Q *ᵥ u) := by rw [hd]; abel
    rw [hx, mulVec_add, hQie, dotProduct_add, add_dotProduct, add_dotProduct,
      Ellipsoid.aux_dot_symm hQiT (lam • (Q *ᵥ u)) d, hQie]
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul, hs]
    ring
  -- the strip term: `C x - y = C d - (1 - λ) w`
  have h2 : (C *ᵥ x - y) ⬝ᵥ (C *ᵥ x - y)
      = (C *ᵥ d) ⬝ᵥ (C *ᵥ d) - 2 * (1 - lam) * (d ⬝ᵥ u) + (1 - lam) ^ 2 * (w ⬝ᵥ w) := by
    have hwv : (1 - lam) • w = (y - C *ᵥ c) - lam • (C *ᵥ (Q *ᵥ u)) := by
      rw [← hδ, hδu]; abel
    have hr : C *ᵥ x - y = C *ᵥ d - (1 - lam) • w := by
      rw [hwv, hd, mulVec_sub, mulVec_add, mulVec_smul]; abel
    rw [hr]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm w (C *ᵥ d), hCa]
    ring
  -- the new form: `dᵀ invQ d = (1 - λ) dᵀ Q⁻¹ d + λ ‖C d‖²`
  have h3 : d ⬝ᵥ P *ᵥ d = (1 - lam) * (d ⬝ᵥ Q⁻¹ *ᵥ d) + lam * ((C *ᵥ d) ⬝ᵥ (C *ᵥ d)) := by
    rw [hP, add_mulVec, smul_mulVec, smul_mulVec, ← mulVec_mulVec, dotProduct_add,
      dotProduct_smul, dotProduct_smul, dotProduct_comm d (Cᵀ *ᵥ _), Ellipsoid.dot_transpose,
      smul_eq_mul, smul_eq_mul]
  -- the strip as a squared bound
  have hxS2 : (C *ᵥ x - y) ⬝ᵥ (C *ᵥ x - y) ≤ φ ^ 2 := by
    rw [dotProduct_self]
    exact pow_le_pow_left₀ (norm₂_nonneg _) hxS 2
  -- the completed square: `dᵀ invQ d ≤ σ²`
  have hquad : d ⬝ᵥ P *ᵥ d ≤ σsq := by
    have e1 := mul_le_mul_of_nonneg_left hxE hl.le
    have e2 := mul_le_mul_of_nonneg_left hxS2 h0
    have key : d ⬝ᵥ P *ᵥ d = (1 - lam) * ((x - c) ⬝ᵥ Q⁻¹ *ᵥ (x - c))
        + lam * ((C *ᵥ x - y) ⬝ᵥ (C *ᵥ x - y)) - lam * (1 - lam) * (δ ⬝ᵥ w) := by
      rw [h3, h1, h2, h4]; ring
    rw [key, hσ]
    linarith
  have hd0 : 0 ≤ d ⬝ᵥ P *ᵥ d := by
    simpa using hPpd.posSemidef.dotProduct_mulVec_nonneg d
  rcases (hd0.trans hquad).lt_or_eq with hpos | hzero
  · -- `σ² > 0`: the sublevel set of `invQ / σ²`
    have hinv : (σsq • P⁻¹) * (σsq⁻¹ • P) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, nonsing_inv_mul P hPu,
        mul_inv_cancel₀ hpos.ne', one_smul]
    rw [Ellipsoid.mem_ofShape_iff (hPpd.inv.smul hpos), inv_eq_right_inv hinv, ← hd,
      smul_mulVec, dotProduct_smul, smul_eq_mul, inv_mul_le_iff₀ hpos, mul_one]
    exact hquad
  · -- `σ² = 0`: the form vanishes, so `x` is the centre
    have hd' : d = 0 := by
      by_contra hne
      have := hPpd.dotProduct_mulVec_pos hne
      simp only [star_trivial] at this
      linarith
    refine ⟨0, by rw [norm₂_zero]; exact zero_le_one, ?_⟩
    rw [mulVec_zero, add_zero]
    exact sub_eq_zero.1 (hd.symm.trans hd')

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
