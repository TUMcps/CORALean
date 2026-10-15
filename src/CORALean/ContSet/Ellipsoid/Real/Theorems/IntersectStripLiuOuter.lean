module

public import CORALean.ContSet.Ellipsoid.Real.Operations.IntersectStripLiu
public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemOfShapeIff
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# The corrected Liu update encloses the intersection

For positive-definite `Q` and `V` and `λ ∈ (0, 1)`, every point `x` with
`(x - c)ᵀ Q⁻¹ (x - c) ≤ σ²_prev` and `(y - C x)ᵀ V⁻¹ (y - C x) ≤ 1` lies in
`intersectStripLiu Q c C V y σ²_prev λ`. With `T = V/λ + C Q Cᵀ/(1 - λ)` (the code's `Q_tmp`),
`w = T⁻¹ δ`, `u = Cᵀ w` and `P = (1 - λ) Q⁻¹ + λ Cᵀ V⁻¹ C`, one has
`P Q Cᵀ = λ (1 - λ) Cᵀ V⁻¹ T`, so `P K = λ Cᵀ V⁻¹` and `P (I - K C) Q / (1 - λ) = I`: the
corrected shape is `P⁻¹`. The center is `c* = c + Q u/(1 - λ)`, `y - C c* = V w/λ - C d` for
`d = x - c*`, and

  `(1 - λ)(x - c)ᵀ Q⁻¹ (x - c) + λ (y - C x)ᵀ V⁻¹ (y - C x) = dᵀ P d + δᵀ w`,

the cross terms `2 dᵀ u` cancelling. The left side is at most `(1 - λ) σ²_prev + λ`, so
`dᵀ P d ≤ σ²`, which is membership in the ellipsoid of shape `σ² P⁻¹`; when `σ² = 0` it forces
`d = 0`, the center. CORA's shape is `(1 - λ)² P⁻¹`, without `σ²`
(`intersectStripLiu1D_counterexample`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.intersectStripLiu_outer {Q : Mat ℝ n n} (hQ : Q.PosDef) (c : Vec ℝ n)
    (C : Mat ℝ m n) {V : Mat ℝ m m} (hV : V.PosDef) (y : Vec ℝ m) (σsqPrev : ℝ) {lam : ℝ}
    (h0 : 0 < lam) (h1 : lam < 1) :
    {x | (x - c) ⬝ᵥ Q⁻¹ *ᵥ (x - c) ≤ σsqPrev} ∩ {x | (y - C *ᵥ x) ⬝ᵥ V⁻¹ *ᵥ (y - C *ᵥ x) ≤ 1}
      ⊆ (Ellipsoid.intersectStripLiu Q c C V y σsqPrev lam).construct := by -- --- PROOF ---
  rintro x ⟨hxE, hxS⟩
  simp only [Set.mem_setOf_eq] at hxE hxS
  have hl : 0 < 1 - lam := by linarith
  have hlne : lam ≠ 0 := h0.ne'
  have hl1ne : 1 - lam ≠ 0 := hl.ne'
  -- the code's `delta` and `Q_tmp`, and the fused inverse shape `P`
  set δ := y - C *ᵥ c with hδ
  set T : Mat ℝ m m := (1 / lam) • V + (1 / (1 - lam)) • (C * Q * Cᵀ) with hT
  set P : Mat ℝ n n := (1 - lam) • Q⁻¹ + lam • (Cᵀ * V⁻¹ * C) with hP
  -- both are positive definite, so invertible
  have hTpd : T.PosDef := by
    have h := hQ.posSemidef.mul_mul_conjTranspose_same C
    rw [conjTranspose_eq_transpose_of_trivial] at h
    exact (hV.smul (by positivity)).add_posSemidef (h.smul (by positivity))
  have hPpd : P.PosDef := by
    have h := hV.inv.posSemidef.conjTranspose_mul_mul_same C
    rw [conjTranspose_eq_transpose_of_trivial] at h
    exact (hQ.inv.smul hl).add_posSemidef (h.smul h0.le)
  have hQu : IsUnit Q.det := (isUnit_iff_isUnit_det Q).1 hQ.isUnit
  have hVu : IsUnit V.det := (isUnit_iff_isUnit_det V).1 hV.isUnit
  have hTu : IsUnit T.det := (isUnit_iff_isUnit_det T).1 hTpd.isUnit
  have hPu : IsUnit P.det := (isUnit_iff_isUnit_det P).1 hPpd.isUnit
  have hQiT : Q⁻¹ᵀ = Q⁻¹ := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hQ.inv.isHermitian.eq
  have hViT : V⁻¹ᵀ = V⁻¹ := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hV.inv.isHermitian.eq
  -- the two quadratic forms are symmetric in their arguments
  have hQs : ∀ a b : Vec ℝ n, a ⬝ᵥ Q⁻¹ *ᵥ b = b ⬝ᵥ Q⁻¹ *ᵥ a := fun a b => by
    rw [← Ellipsoid.dot_transpose, hQiT, dotProduct_comm]
  have hVs : ∀ a b : Vec ℝ m, a ⬝ᵥ V⁻¹ *ᵥ b = b ⬝ᵥ V⁻¹ *ᵥ a := fun a b => by
    rw [← Ellipsoid.dot_transpose, hViT, dotProduct_comm]
  -- `P Q Cᵀ = λ (1 - λ) Cᵀ V⁻¹ T`, so `P K = λ Cᵀ V⁻¹` and the corrected shape is `P⁻¹`
  have hM : P * Q * Cᵀ = (lam * (1 - lam)) • (Cᵀ * V⁻¹ * T) := by
    simp only [hP, hT, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      ← Matrix.mul_assoc, nonsing_inv_mul Q hQu, Matrix.one_mul]
    rw [Matrix.mul_assoc Cᵀ V⁻¹ V, nonsing_inv_mul V hVu, Matrix.mul_one]
    match_scalars <;> field_simp
  have hPK : P * ((1 / (1 - lam)) • (Q * Cᵀ * T⁻¹)) = lam • (Cᵀ * V⁻¹) := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hM, Matrix.smul_mul,
      Matrix.mul_assoc, mul_nonsing_inv T hTu, Matrix.mul_one, smul_smul]
    congr 1
    field_simp
  have hshape : (1 / (1 - lam)) • ((1 - (1 / (1 - lam)) • (Q * Cᵀ * T⁻¹) * C) * Q) = P⁻¹ := by
    symm
    apply inv_eq_right_inv
    rw [Matrix.mul_smul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hPK]
    simp only [hP, Matrix.add_mul, Matrix.smul_mul, nonsing_inv_mul Q hQu, Matrix.mul_assoc]
    rw [add_sub_cancel_right, smul_smul, one_div, inv_mul_cancel₀ hl1ne, one_smul]
  -- `w = T⁻¹ δ` and `u = Cᵀ w`
  set w := T⁻¹ *ᵥ δ with hw
  have hTw : T *ᵥ w = δ := by rw [hw, mulVec_mulVec, mul_nonsing_inv T hTu, one_mulVec]
  have hKδ : ((1 / (1 - lam)) • (Q * Cᵀ * T⁻¹)) *ᵥ δ = (1 / (1 - lam)) • (Q *ᵥ (Cᵀ *ᵥ w)) := by
    rw [smul_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← hw]
  clear_value w
  obtain ⟨u, hu⟩ : ∃ u, u = Cᵀ *ᵥ w := ⟨_, rfl⟩
  rw [← hu] at hKδ
  have hδu : δ = (1 / lam) • (V *ᵥ w) + (1 / (1 - lam)) • (C *ᵥ (Q *ᵥ u)) := by
    rw [← hTw, hT, add_mulVec, smul_mulVec, smul_mulVec, hu, mulVec_mulVec, mulVec_mulVec]
  -- the goal, at the shape `σ² P⁻¹` and the center `c + Q u / (1 - λ)`
  show x ∈ (Ellipsoid.ofShape
    (((1 - lam) * σsqPrev + lam - δ ⬝ᵥ T⁻¹ *ᵥ δ) •
      ((1 / (1 - lam)) • ((1 - (1 / (1 - lam)) • (Q * Cᵀ * T⁻¹) * C) * Q)))
      (c + ((1 / (1 - lam)) • (Q * Cᵀ * T⁻¹)) *ᵥ δ)).construct
  rw [hshape, hKδ, ← hw]
  set σsq := (1 - lam) * σsqPrev + lam - δ ⬝ᵥ w with hσ
  set a := 1 / (1 - lam) with ha
  obtain ⟨d, hd⟩ : ∃ d, d = x - (c + a • (Q *ᵥ u)) := ⟨_, rfl⟩
  -- the scalar pieces: `Q⁻¹ (a Q u) = a u`, `V⁻¹ V w = w` and `(C z)ᵀ w = zᵀ u`
  have hQie : Q⁻¹ *ᵥ (a • (Q *ᵥ u)) = a • u := by
    rw [mulVec_smul, mulVec_mulVec, nonsing_inv_mul Q hQu, one_mulVec]
  have hVie : V⁻¹ *ᵥ (V *ᵥ w) = w := by
    rw [mulVec_mulVec, nonsing_inv_mul V hVu, one_mulVec]
  have hCa : ∀ z, (C *ᵥ z) ⬝ᵥ w = z ⬝ᵥ u := fun z => by
    rw [hu, dotProduct_comm, ← Ellipsoid.dot_transpose, dotProduct_comm]
  set s := (Q *ᵥ u) ⬝ᵥ u with hs
  set v := (V *ᵥ w) ⬝ᵥ w with hv
  -- `δᵀ w = vᵀ w / λ + a s`
  have h4 : δ ⬝ᵥ w = (1 / lam) * v + a * s := by
    conv_lhs => rw [hδu]
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, hCa, smul_eq_mul, smul_eq_mul]
  -- the ellipsoid term: `x - c = d + a Q u`
  have hE : (x - c) ⬝ᵥ Q⁻¹ *ᵥ (x - c) = d ⬝ᵥ Q⁻¹ *ᵥ d + 2 * a * (d ⬝ᵥ u) + a ^ 2 * s := by
    have hx : x - c = d + a • (Q *ᵥ u) := by rw [hd]; abel
    rw [hx, mulVec_add, hQie, dotProduct_add, add_dotProduct, add_dotProduct,
      hQs (a • (Q *ᵥ u)) d, hQie]
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul, hs]
    ring
  -- the measurement term: `y - C x = V w / λ - C d`
  have hS : (y - C *ᵥ x) ⬝ᵥ V⁻¹ *ᵥ (y - C *ᵥ x)
      = (1 / lam) ^ 2 * v - 2 * (1 / lam) * (d ⬝ᵥ u) + (C *ᵥ d) ⬝ᵥ V⁻¹ *ᵥ (C *ᵥ d) := by
    have hr : y - C *ᵥ x = (1 / lam) • (V *ᵥ w) - C *ᵥ d := by
      have : y - C *ᵥ x = δ - C *ᵥ d - a • (C *ᵥ (Q *ᵥ u)) := by
        rw [hδ, hd, mulVec_sub, mulVec_add, mulVec_smul]; abel
      rw [this, hδu]; abel
    rw [hr, mulVec_sub, mulVec_smul, hVie, dotProduct_sub, sub_dotProduct, sub_dotProduct]
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [hVs (V *ᵥ w) (C *ᵥ d), hVie, hCa, ← hv]
    ring
  -- the new form: `dᵀ P d = (1 - λ) dᵀ Q⁻¹ d + λ (C d)ᵀ V⁻¹ (C d)`
  have h3 : d ⬝ᵥ P *ᵥ d
      = (1 - lam) * (d ⬝ᵥ Q⁻¹ *ᵥ d) + lam * ((C *ᵥ d) ⬝ᵥ V⁻¹ *ᵥ (C *ᵥ d)) := by
    rw [hP, add_mulVec, smul_mulVec, smul_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_comm d (Cᵀ *ᵥ _),
      Ellipsoid.dot_transpose, dotProduct_comm (V⁻¹ *ᵥ (C *ᵥ d)), smul_eq_mul, smul_eq_mul]
  -- the completed square: `dᵀ P d ≤ σ²`
  have hquad : d ⬝ᵥ P *ᵥ d ≤ σsq := by
    have e1 := mul_le_mul_of_nonneg_left hxE hl.le
    have e2 := mul_le_mul_of_nonneg_left hxS h0.le
    have key : d ⬝ᵥ P *ᵥ d = (1 - lam) * ((x - c) ⬝ᵥ Q⁻¹ *ᵥ (x - c))
        + lam * ((y - C *ᵥ x) ⬝ᵥ V⁻¹ *ᵥ (y - C *ᵥ x)) - δ ⬝ᵥ w := by
      rw [h3, hE, hS, h4, ha]
      field_simp
      ring
    rw [key, hσ]
    linarith
  have hd0 : 0 ≤ d ⬝ᵥ P *ᵥ d := by
    simpa using hPpd.posSemidef.dotProduct_mulVec_nonneg d
  rcases (hd0.trans hquad).lt_or_eq with hpos | hzero
  · -- `σ² > 0`: the sublevel set of `P / σ²`
    have hinv : (σsq • P⁻¹) * (σsq⁻¹ • P) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, nonsing_inv_mul P hPu,
        mul_inv_cancel₀ hpos.ne', one_smul]
    rw [Ellipsoid.mem_ofShape_iff (hPpd.inv.smul hpos), inv_eq_right_inv hinv, ← hd,
      smul_mulVec, dotProduct_smul, smul_eq_mul, inv_mul_le_iff₀ hpos, mul_one]
    exact hquad
  · -- `σ² = 0`: the form vanishes, so `x` is the center
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
