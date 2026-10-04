import CORALean.ContSet.Ellipsoid.Real.Operations.Radius
import CORALean.ContSet.Ellipsoid.Real.Theorems.DotTranspose
import CORALean.ContSet.Ellipsoid.Real.Theorems.MemConstruct
import CORALean.ContSet.Ellipsoid.Real.Theorems.QMemConstruct

/-!
# The first radius is the largest distance from the centre

CORA's `radius(E)` (`i = 1`) is the radius of the smallest hyperball around the centre that
holds the ellipsoid: `sqrt` of the largest eigenvalue `λ₀` of `Q = G Gᵀ` is the greatest
distance `‖x - q‖₂` over the ellipsoid. Bound: for `v = G u`, `‖v‖² ≤ ‖Gᵀ v‖ ‖u‖` and
`‖Gᵀ v‖² = vᵀ Q v ≤ λ₀ ‖v‖²` (Rayleigh, from the spectral theorem). Attained: at `q + G u*`,
`u* = Gᵀ v / sqrt λ₀`, `v` the unit eigenvector of `λ₀`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- Rayleigh: no eigenvalue exceeds the first (sorted in decreasing order)
theorem Ellipsoid.aux_rayleigh (A : Mat ℝ n n) (hA : A.IsHermitian) (h0 : 0 < Fintype.card (Fin n))
    (v : Vec ℝ n) : v ⬝ᵥ (A *ᵥ v) ≤ hA.eigenvalues₀ ⟨0, h0⟩ * (v ⬝ᵥ v) := by -- --- PROOF ---
  set U : Mat ℝ n n := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  set D : Mat ℝ n n := Matrix.diagonal hA.eigenvalues with hD
  have hspec : A = U * D * Uᵀ := by
    have := hA.spectral_theorem
    simpa [hU, hD, Matrix.star_eq_conjTranspose, Function.comp_def] using this
  have hUU : U * Uᵀ = 1 := by
    have := Unitary.coe_mul_star_self hA.eigenvectorUnitary
    simpa [hU, Matrix.star_eq_conjTranspose] using this
  -- the coordinates `w` of `v` in the eigenbasis
  set w : Vec ℝ n := Uᵀ *ᵥ v with hw
  have hv : v ⬝ᵥ v = w ⬝ᵥ w := by
    have hUtU : Uᵀ * U = 1 := by
      have := Unitary.coe_star_mul_self hA.eigenvectorUnitary
      simpa [hU, Matrix.star_eq_conjTranspose] using this
    rw [hw, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_transpose,
      Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  have hq : v ⬝ᵥ (A *ᵥ v) = ∑ i, hA.eigenvalues i * w i ^ 2 := by
    have h1 : v ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ ((U * D * Uᵀ) *ᵥ v) := congrArg (fun M => v ⬝ᵥ (M *ᵥ v)) hspec
    rw [h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose]
    simp only [hD, hw, Matrix.mulVec_diagonal, dotProduct, sq]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hq, hv, dotProduct, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  -- each eigenvalue is at most the first
  have hle : hA.eigenvalues i ≤ hA.eigenvalues₀ ⟨0, h0⟩ :=
    hA.eigenvalues₀_antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
  nlinarith [sq_nonneg (w i)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.isGreatest_radius (E : Ellipsoid n) (hn : 1 ≤ n) :
    IsGreatest ((fun x => ‖x - E.q‖₂) '' E.construct)
      (E.radius 1 hn ⟨0, one_pos⟩) := by -- --- PROOF ---
  -- the shape matrix, its first eigenvalue `l0`
  have hQ : E.shape.IsHermitian := by
    simpa [Ellipsoid.shape] using Matrix.isHermitian_mul_conjTranspose_self E.G
  have h0 : 0 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact hn
  set l0 := hQ.eigenvalues₀ ⟨0, h0⟩ with hl0
  have hrad : E.radius 1 hn ⟨0, one_pos⟩ = Real.sqrt l0 := rfl
  rw [hrad]
  -- `‖Gᵀ v‖² = vᵀ Q v`
  have hGt : ∀ v : Vec ℝ n, ‖E.Gᵀ *ᵥ v‖₂ ^ 2 = v ⬝ᵥ (E.shape *ᵥ v) := fun v => by
    rw [← dotProduct_self, Ellipsoid.dot_transpose, Ellipsoid.shape, ← Matrix.mulVec_mulVec]
  refine ⟨?_, ?_⟩
  · -- attained at `q + G u*`
    by_cases hl : l0 ≤ 0
    · -- no spread: the centre itself
      refine ⟨E.q, E.q_mem_construct, ?_⟩
      have : Real.sqrt l0 = 0 := Real.sqrt_eq_zero_of_nonpos hl
      simp [this, norm₂_zero]
    · have hl := not_le.mp hl
      -- a unit eigenvector `v` of `l0`
      set j0 : Fin n := Fintype.equivOfCardEq (Fintype.card_fin _) ⟨0, h0⟩ with hj0
      set v : Vec ℝ n := ⇑(hQ.eigenvectorBasis j0) with hv
      have hQv : E.shape *ᵥ v = l0 • v := by
        have := hQ.mulVec_eigenvectorBasis j0
        simpa [Matrix.IsHermitian.eigenvalues, hj0, hl0] using this
      have hvn : ‖v‖₂ = 1 := by
        rw [← norm_toEuclidean]
        exact (hQ.eigenvectorBasis).norm_eq_one j0
      -- `u* = Gᵀ v / sqrt l0` has unit length and `G u* = sqrt l0 • v`
      have hsq : Real.sqrt l0 ^ 2 = l0 := Real.sq_sqrt hl.le
      have hpos : 0 < Real.sqrt l0 := Real.sqrt_pos.mpr hl
      set u : Vec ℝ E.k := (Real.sqrt l0)⁻¹ • (E.Gᵀ *ᵥ v) with hu
      have hGu : E.G *ᵥ u = Real.sqrt l0 • v := by
        rw [hu, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
        change (Real.sqrt l0)⁻¹ • (E.shape *ᵥ v) = _
        rw [hQv, smul_smul]
        congr 1
        calc (Real.sqrt l0)⁻¹ * l0 = (Real.sqrt l0)⁻¹ * (Real.sqrt l0 * Real.sqrt l0) := by
              rw [Real.mul_self_sqrt hl.le]
          _ = Real.sqrt l0 := by field_simp
      -- `u*` is in the unit ball: `‖Gᵀ v‖₂ = sqrt l0`
      have hun : ‖u‖₂ ≤ 1 := by
        rw [hu, norm₂_smul, abs_of_pos (inv_pos.mpr hpos)]
        have h2 : ‖E.Gᵀ *ᵥ v‖₂ ^ 2 = l0 := by
          rw [hGt, hQv, dotProduct_smul, dotProduct_self, hvn]; simp
        have h3 : ‖E.Gᵀ *ᵥ v‖₂ = Real.sqrt l0 := by
          rw [← h2]; exact (Real.sqrt_sq (norm₂_nonneg _)).symm
        rw [h3, inv_mul_cancel₀ hpos.ne']
      refine ⟨E.q + E.G *ᵥ u, Ellipsoid.mem_construct hun, ?_⟩
      simp only [add_sub_cancel_left, hGu]
      rw [norm₂_smul, hvn, mul_one, abs_of_pos hpos]
  · -- the bound
    rintro _ ⟨x, ⟨u, hu, rfl⟩, rfl⟩
    simp only [add_sub_cancel_left]
    set v := E.G *ᵥ u with hv
    have h1 : ‖v‖₂ ^ 2 ≤ ‖E.Gᵀ *ᵥ v‖₂ := by
      rw [← dotProduct_self]
      calc v ⬝ᵥ v = (E.Gᵀ *ᵥ v) ⬝ᵥ u := by rw [Ellipsoid.dot_transpose]
        _ ≤ ‖E.Gᵀ *ᵥ v‖₂ * ‖u‖₂ := dotProduct_le_norm₂_mul_norm₂ _ _
        _ ≤ ‖E.Gᵀ *ᵥ v‖₂ * 1 := mul_le_mul_of_nonneg_left hu (norm₂_nonneg _)
        _ = _ := mul_one _
    have h2 : ‖E.Gᵀ *ᵥ v‖₂ ^ 2 ≤ l0 * ‖v‖₂ ^ 2 := by
      rw [hGt, ← dotProduct_self]
      exact Ellipsoid.aux_rayleigh E.shape hQ h0 v
    -- `‖v‖⁴ ≤ ‖Gᵀ v‖² ≤ l0 ‖v‖²`
    rcases (norm₂_nonneg v).eq_or_lt with h | h
    · rw [← h]; exact Real.sqrt_nonneg _
    · apply Real.le_sqrt_of_sq_le
      have h4 : (‖v‖₂ ^ 2) ^ 2 ≤ l0 * ‖v‖₂ ^ 2 :=
        calc (‖v‖₂ ^ 2) ^ 2 ≤ ‖E.Gᵀ *ᵥ v‖₂ ^ 2 :=
              pow_le_pow_left₀ (sq_nonneg _) h1 2
          _ ≤ _ := h2
      have h5 : 0 < ‖v‖₂ ^ 2 := by positivity
      nlinarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
