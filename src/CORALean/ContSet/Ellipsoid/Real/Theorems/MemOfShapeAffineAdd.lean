module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemOfShapeIff
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# An affine image of an ellipsoid plus a second ellipsoid, at a weight `p`

For positive-definite `Q` and `W` and `p ∈ (0, 1)`: if `x ∈ E(Q, c)` and `w ∈ E(W, 0)`, then `M x +
u + w` lies in the ellipsoid of center `M c + u` and shape `N = (1 - p)⁻¹ M Q Mᵀ + p⁻¹ W`, which is
positive definite. This is the prediction of CORA's observers `ESO-A` and `ESO-B` at the level `1`.
With `z = M (x - c) + w` and `v = N⁻¹ z`, `zᵀ N⁻¹ z = vᵀ N v`. The bound `2 aᵀ e ≤ k aᵀ P a + eᵀ P⁻¹
e / k`, at `a = Mᵀ v`, `e = x - c`, `P = Q`, `k = (1 - p)⁻¹` and at `a = v`, `e = w`, `P = W`, `k =
p⁻¹`, sums to `2 vᵀ z ≤ vᵀ N v + (1 - p) + p`, so `vᵀ z ≤ 1`.

## Inputs
* `Q` – shape matrix
* `W` – second shape matrix
* `M` – matrix
* `p` – weight in `(0, 1)`
* `c` – center
* `u` – offset
* `x` – point of the first ellipsoid
* `w` – point of the second ellipsoid

## Hypotheses
* `hQ` – `Q` positive definite
* `hW` – `W` positive definite
* `hp0` – `0 < p`
* `hp1` – `p < 1`
* `hx` – `x` in `E(Q, c)`
* `hw` – `w` in `E(W, 0)`

## Conclusion
* `M x + u + w` lies in the ellipsoid of the weighted shape sum
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

/-- `2 aᵀ e ≤ k aᵀ P a + eᵀ P⁻¹ e / k` for positive-definite `P` and `k > 0`. -/
theorem Ellipsoid.aux_two_dot_le {P : Mat ℝ n n} (hP : P.PosDef) (a e : Vec ℝ n) {k : ℝ}
    (hk : 0 < k) : -- --- CONCL ---
    2 * (a ⬝ᵥ e) ≤ k * (a ⬝ᵥ P *ᵥ a) + (e ⬝ᵥ P⁻¹ *ᵥ e) / k := by -- --- PROOF ---
  have hPu : IsUnit P.det := (isUnit_iff_isUnit_det P).1 hP.isUnit
  have hPiT : P⁻¹ᵀ = P⁻¹ := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hP.inv.isHermitian.eq
  have hPa : P⁻¹ *ᵥ (P *ᵥ a) = a := by
    rw [mulVec_mulVec, nonsing_inv_mul P hPu, one_mulVec]
  -- `(P a)ᵀ P⁻¹ e = aᵀ e`
  have hs : (P *ᵥ a) ⬝ᵥ P⁻¹ *ᵥ e = a ⬝ᵥ e := by
    rw [← Ellipsoid.dot_transpose, hPiT, dotProduct_comm, hPa, dotProduct_comm]
  have h0 : 0 ≤ (k • (P *ᵥ a) - e) ⬝ᵥ P⁻¹ *ᵥ (k • (P *ᵥ a) - e) := by
    simpa using hP.inv.posSemidef.dotProduct_mulVec_nonneg (k • (P *ᵥ a) - e)
  have hexp : (k • (P *ᵥ a) - e) ⬝ᵥ P⁻¹ *ᵥ (k • (P *ᵥ a) - e)
      = k * k * (a ⬝ᵥ P *ᵥ a) - 2 * k * (a ⬝ᵥ e) + e ⬝ᵥ P⁻¹ *ᵥ e := by
    rw [mulVec_sub, mulVec_smul, hPa, dotProduct_sub, sub_dotProduct, sub_dotProduct,
      smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, hs,
      dotProduct_comm (P *ᵥ a) a, dotProduct_comm e a]
    simp only [smul_eq_mul]
    ring
  rw [hexp] at h0
  have key : k * (2 * (a ⬝ᵥ e)) ≤ k * (k * (a ⬝ᵥ P *ᵥ a) + (e ⬝ᵥ P⁻¹ *ᵥ e) / k) := by
    rw [mul_add, mul_div_cancel₀ _ hk.ne']
    have e1 : k * (2 * (a ⬝ᵥ e)) = 2 * k * (a ⬝ᵥ e) := by ring
    have e2 : k * (k * (a ⬝ᵥ P *ᵥ a)) = k * k * (a ⬝ᵥ P *ᵥ a) := by ring
    rw [e1, e2]
    linarith
  exact le_of_mul_le_mul_left key hk


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.mem_ofShape_affine_add {Q : Mat ℝ n n} (hQ : Q.PosDef) {W : Mat ℝ m m}
    (hW : W.PosDef) (M : Mat ℝ m n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (c : Vec ℝ n)
    (u : Vec ℝ m) {x : Vec ℝ n} {w : Vec ℝ m} (hx : x ∈ (Ellipsoid.ofShape Q c).construct)
    (hw : w ∈ (Ellipsoid.ofShape W 0).construct) : -- --- CONCL ---
    ((1 - p)⁻¹ • (M * Q * Mᵀ) + p⁻¹ • W).PosDef ∧
      M *ᵥ x + u + w ∈ (Ellipsoid.ofShape ((1 - p)⁻¹ • (M * Q * Mᵀ) + p⁻¹ • W)
        (M *ᵥ c + u)).construct := by -- --- PROOF ---
  rw [Ellipsoid.mem_ofShape_iff hQ] at hx
  rw [Ellipsoid.mem_ofShape_iff hW, sub_zero] at hw
  have hq : 0 < 1 - p := by linarith
  set N := (1 - p)⁻¹ • (M * Q * Mᵀ) + p⁻¹ • W with hN
  have hNpd : N.PosDef := by
    have h := hQ.posSemidef.mul_mul_conjTranspose_same M
    rw [conjTranspose_eq_transpose_of_trivial] at h
    have h' := (hW.smul (inv_pos.2 hp0)).add_posSemidef (h.smul (inv_nonneg.2 hq.le))
    rwa [add_comm] at h'
  refine ⟨hNpd, ?_⟩
  rw [Ellipsoid.mem_ofShape_iff hNpd]
  have hNu : IsUnit N.det := (isUnit_iff_isUnit_det N).1 hNpd.isUnit
  have hz : M *ᵥ x + u + w - (M *ᵥ c + u) = M *ᵥ (x - c) + w := by
    rw [mulVec_sub]; abel
  rw [hz]
  set z := M *ᵥ (x - c) + w with hzdef
  set v := N⁻¹ *ᵥ z with hv
  have hNv : N *ᵥ v = z := by rw [hv, mulVec_mulVec, mul_nonsing_inv N hNu, one_mulVec]
  -- `vᵀ N v = (1 - p)⁻¹ (Mᵀ v)ᵀ Q (Mᵀ v) + p⁻¹ vᵀ W v`, and it is `vᵀ z`
  have hvNv : v ⬝ᵥ N *ᵥ v
      = (1 - p)⁻¹ * ((Mᵀ *ᵥ v) ⬝ᵥ Q *ᵥ (Mᵀ *ᵥ v)) + p⁻¹ * (v ⬝ᵥ W *ᵥ v) := by
    rw [hN, add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
      dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mulVec_mulVec, ← mulVec_mulVec,
      ← Ellipsoid.dot_transpose M v]
  have hvN : v ⬝ᵥ N *ᵥ v = v ⬝ᵥ z := by rw [hNv]
  have hvz : v ⬝ᵥ z = (Mᵀ *ᵥ v) ⬝ᵥ (x - c) + v ⬝ᵥ w := by
    rw [hzdef, dotProduct_add, Ellipsoid.dot_transpose]
  -- the two bounds, each summand's form at most one
  have h1 := Ellipsoid.aux_two_dot_le hQ (Mᵀ *ᵥ v) (x - c) (inv_pos.2 hq)
  have h2 := Ellipsoid.aux_two_dot_le hW v w (inv_pos.2 hp0)
  rw [div_inv_eq_mul] at h1 h2
  have b1 := mul_le_mul_of_nonneg_right hx hq.le
  have b2 := mul_le_mul_of_nonneg_right hw hp0.le
  rw [dotProduct_comm]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
