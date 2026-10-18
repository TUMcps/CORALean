module

public import CORALean.ContSet.Ellipsoid.Float.Operations.AbsorbRounding
public import CORALean.ContSet.Ellipsoid.Float.Theorems.AddSubMemNominalSet
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic
public import CORALean.ContSet.Ellipsoid.Float.Theorems.InflateSubPosSemidef
public import CORALean.ContSet.Ellipsoid.Float.Theorems.IsPsdSound
public import CORALean.ContSet.Ellipsoid.Real.Theorems.ConstructOfFactor
public import CORALean.ContSet.Ellipsoid.Real.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MatPlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact
public import CORALean.ContSet.Interval.Float.Theorems.SmulOuter

@[expose] public section

/-!
# `Ellipsoid.absorbRounding` loses no point

A point is a point `y` of the nominal part plus a point `e` of the box. Each coordinate of `e` is
at most the box's larger end magnitude there, so `Σ eᵢ² ≤ ρ²` (`sq_sum_le_sqSumUp`) and `e` lies
in the ball of radius `√ρ²`, the ellipsoid of factor `√ρ² I` (`aux_mem_ball`). For a certified
shape the exact layer's `plus_outer` at the scalings `√(1 + 1/β)`, `√(1 + β)` (rounded up, which
keeps the reciprocal squares summing to at most one, `aux_weights_admissible`) puts `y + e` in the
ellipsoid of `(1 + 1/β) Q + (1 + β) ρ² I` about the stored center, which the stored shape
dominates (`inflate_sub_posSemidef`), so `y + e` is in the result's nominal part
(`add_sub_mem_nominalSet`) and the origin box adds nothing. A box with `ρ² ≤ 0` holds only the
origin, and an uncertified shape is returned unchanged.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open CORALean Pointwise FloatOps SoundFloatArithmetic InflatedContSet
open scoped Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A vector whose squares sum to at most `r²` is in the ball of radius `r ≥ 0`, the ellipsoid of
factor `r I` about the origin. -/
theorem Ellipsoid.aux_mem_ball {r : ℝ} (hr : 0 ≤ r) {e : Vec ℝ n} (he : ∑ i, e i ^ 2 ≤ r ^ 2) :
    e ∈ (Real.Ellipsoid.ofFactor (r • (1 : Mat ℝ n n)) 0).construct := by -- --- PROOF ---
  rw [Real.Ellipsoid.construct_ofFactor]
  rcases eq_or_lt_of_le hr with h0 | hpos
  · -- a ball of radius `0` is the origin, and so is `e`
    subst h0
    have hz : e = 0 := funext fun i => by
      have h : e i ^ 2 ≤ ∑ j, e j ^ 2 := Finset.single_le_sum (f := fun j => e j ^ 2)
        (fun j _ => sq_nonneg (e j)) (Finset.mem_univ i)
      have : e i ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    refine ⟨0, by rw [norm₂_zero]; exact zero_le_one, ?_⟩
    rw [hz, Matrix.mulVec_zero, add_zero]
  · -- otherwise `e / r` is in the unit ball
    have hn : ‖e‖₂ ≤ r := by
      rw [show r = Real.sqrt (r ^ 2) from (Real.sqrt_sq hr).symm]
      exact Real.sqrt_le_sqrt he
    refine ⟨r⁻¹ • e, ?_, ?_⟩
    · rw [norm₂_smul, abs_of_pos (inv_pos.mpr hpos)]
      calc r⁻¹ * ‖e‖₂ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hr)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
    · rw [Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, mul_inv_cancel₀ (ne_of_gt hpos),
        one_smul, zero_add]

/-- The weights `a ≥ 1 + 1/β` and `c ≥ 1 + β` at any `β > 0` have reciprocals summing to at most
one, which is what `plus_outer` asks of the squared scalings. -/
theorem Ellipsoid.aux_weights_admissible {β a c : ℝ} (hβ : 0 < β) (ha : 1 + 1 / β ≤ a)
    (hc : 1 + β ≤ c) : 1 / a + 1 / c ≤ 1 := by -- --- PROOF ---
  have e₁ : 1 / a ≤ 1 / (1 + 1 / β) := one_div_le_one_div_of_le (by positivity) ha
  have e₂ : 1 / c ≤ 1 / (1 + β) := one_div_le_one_div_of_le (by positivity) hc
  have e₃ : 1 / (1 + 1 / β) + 1 / (1 + β) = 1 := by
    field_simp
    ring
  linarith


-- =======================================  MAIN THEOREM  ======================================= --

/-- `absorbRounding` contains the set. -/
theorem Ellipsoid.absorbRounding_outer (k : ℕ) (E : Ellipsoid 𝕋 n) :
    E.construct ⊆ (E.absorbRounding k).construct := by -- --- PROOF ---
  rintro _ ⟨y, hy, e, he, rfl⟩
  -- the box's point squared-sums to at most `ρ²`
  have hρ : ∑ i, e i ^ 2 ≤ toReal (sqSumUp E.I_error.normMag) :=
    sq_sum_le_sqSumUp fun j => by
      have h := abs_le_max_abs_abs (Interval.mem_vec_iff.mp he j).1 (Interval.mem_vec_iff.mp he j).2
      rw [Interval.normMag, toReal_maximum, toReal_absolute, toReal_absolute]
      exact h
  have h0 : (0 : Vec ℝ n) ∈ (Interval.origin n : Interval (Vec 𝕋 n)).construct := by
    rw [Interval.origin_exact]
    rfl
  unfold Ellipsoid.absorbRounding
  by_cases hpsd : Ellipsoid.isPsd E.Q = true
  · rw [if_pos hpsd]
    by_cases hz : le (sqSumUp E.I_error.normMag) zero = true
    · -- the box holds only the origin
      rw [if_pos hz]
      have hle := toReal_le_of_le hz
      rw [toReal_zero] at hle
      have he0 : e = 0 := funext fun i => by
        have h : e i ^ 2 ≤ ∑ j, e j ^ 2 := Finset.single_le_sum (f := fun j => e j ^ 2)
          (fun j _ => sq_nonneg (e j)) (Finset.mem_univ i)
        have : e i ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
        exact pow_eq_zero_iff two_ne_zero |>.mp this
      subst he0
      exact ⟨y, hy, 0, h0, rfl⟩
    · rw [if_neg hz]
      dsimp only
      -- the nominal ellipsoid, the ball, and the weights
      set ρ2 := sqSumUp E.I_error.normMag
      set β₀ := sqrtUp k (divUp (sumUp fun i => E.Q i i) (mulDown (nsmulUp n one) ρ2))
      set β := if ltStrict zero β₀ = true then β₀ else one with hβdef
      set a := addUp one (divUp one β)
      set c := addUp one β
      -- `β` is positive, and the weights are at least `1 + 1/β` and `1 + β`
      have hβ : 0 < toReal β := by
        rw [hβdef]
        split_ifs with h
        · simpa [toReal_zero] using toReal_lt_of_ltStrict h
        · rw [toReal_one]; exact one_pos
      have ha : 1 + 1 / toReal β ≤ toReal a := by
        have h₁ := div_le_divUp one β hβ
        have h₂ := add_le_addUp (one : 𝕋) (divUp one β)
        rw [toReal_one] at h₁ h₂
        linarith
      have hc : 1 + toReal β ≤ toReal c := by
        have h₂ := add_le_addUp (one : 𝕋) β
        rw [toReal_one] at h₂
        linarith
      have hβ' : 0 < 1 / toReal β := by positivity
      have ha0 : 0 < toReal a := by linarith
      have hc0 : 0 < toReal c := by linarith
      have hρ0 : 0 ≤ toReal ρ2 := le_trans (Finset.sum_nonneg fun i _ => sq_nonneg (e i)) hρ
      -- the nominal part is the certified ellipsoid, and the box lies in the ball
      have hpsd' := Ellipsoid.posSemidef_of_isPsd hpsd
      set A₁ : Real.Ellipsoid n := ⟨toRealMat E.Q, toRealVec E.q, hpsd'⟩
      set r := Real.sqrt (toReal ρ2)
      set A₂ := Real.Ellipsoid.ofFactor (r • (1 : Mat ℝ n n)) 0
      have hy₁ : y ∈ A₁.construct := by
        have : (InflatedContSet.nominal E).ellipsoid = A₁ := Ellipsoid.nominal_of_psd hpsd'
        rw [← this]
        exact hy
      have he₂ : e ∈ A₂.construct :=
        Ellipsoid.aux_mem_ball (Real.sqrt_nonneg _) (by rw [Real.sq_sqrt hρ0]; exact hρ)
      -- the exact layer's enclosure of the sum at the scalings `√a`, `√c`
      have hsa : Real.sqrt (toReal a) ^ 2 = toReal a := Real.sq_sqrt ha0.le
      have hsc : Real.sqrt (toReal c) ^ 2 = toReal c := Real.sq_sqrt hc0.le
      set F := Real.Ellipsoid.plus (Real.sqrt (toReal a)) (Real.sqrt (toReal c)) A₁ A₂
      have hyF : y + e ∈ F.construct :=
        Real.Ellipsoid.plus_outer _ _ A₁ A₂ (Real.sqrt_ne_zero'.mpr ha0)
          (Real.sqrt_ne_zero'.mpr hc0)
          (by rw [hsa, hsc]; exact Ellipsoid.aux_weights_admissible hβ ha hc)
          ⟨y, hy₁, e, he₂, rfl⟩
      -- the interval matrix holds `F.Q`, which the stored shape dominates
      have hX : F.Q ∈ (Interval.matPlus (Interval.smul a a (Interval.point E.Q))
          ⟨diagonalBlock fun _ => mulDown c ρ2, diagonalBlock fun _ => mulUp c ρ2⟩).construct := by
        refine Interval.matPlus_outer _ _ ?_ ?_
        · rw [hsa]
          exact Interval.smul_outer le_rfl le_rfl _ (Interval.mem_point E.Q)
        · rw [hsc, Interval.mem_mat_iff]
          -- the ball's shape, entrywise between the two roundings of `c ρ²` on the diagonal
          intro i j
          have hQ : (toReal c • A₂.Q) i j = toReal c * toReal ρ2 * (1 : Mat ℝ n n) i j := by
            show toReal c * ((r • (1 : Mat ℝ n n)) * (r • (1 : Mat ℝ n n))ᵀ) i j = _
            rw [Matrix.transpose_smul, Matrix.transpose_one, smul_mul_smul, mul_one,
              Matrix.smul_apply, smul_eq_mul, ← pow_two, Real.sq_sqrt hρ0]
            ring
          rw [hQ, toReal_diagonalBlock, toReal_diagonalBlock]
          by_cases hij : i = j
          · subst hij
            simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, mul_one, toRealVec]
            exact ⟨mulDown_le_mul _ _, mul_le_mulUp _ _⟩
          · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, mul_zero]
            exact ⟨le_rfl, le_rfl⟩
      have hsym : ∀ i j, F.Q i j = F.Q j i := fun i j => by
        have h := F.psd.isHermitian.eq
        simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at h
        exact (congrFun (congrFun h i) j).symm
      have hdom := Ellipsoid.inflate_sub_posSemidef (Interval.mem_mat_iff.mp hX) hsym
      -- `y + e` about the stored center, and the origin box adds nothing
      have hmem := Ellipsoid.add_sub_mem_nominalSet (E := ⟨_, E.q, Interval.origin n⟩)
        (Or.inr hdom) hyF
      have hFq : F.q = toRealVec E.q := by
        show toRealVec E.q + 0 = _
        rw [add_zero]
      rw [hFq, add_sub_cancel] at hmem
      exact ⟨y + e, hmem, 0, h0, add_zero _⟩
  · -- an uncertified shape: nothing changes
    rw [if_neg hpsd]
    exact ⟨y, hy, e, he, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
