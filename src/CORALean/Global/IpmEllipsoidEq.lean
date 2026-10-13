module

public import CORALean.Global.IpmEllipsoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# The interval of the ellipsoid predictor

[1, Eq. 7]: for the ellipsoidal model [1, Eq. 3], [1, Eq. 5] (`ipmEllipsoid`) with `P ≻ 0`
and `γ ≥ 0`, `I(ϕ) = [cᵀϕ - (√(ϕᵀPϕ) + γ), cᵀϕ + (√(ϕᵀPϕ) + γ)]`, "by similar considerations" as
[1, Eq. 6]. Exactly that interval: the enclosure is Cauchy-Schwarz in the inner product of
`P⁻¹`, `|ρᵀϕ| ≤ √(ρᵀP⁻¹ρ) √(ϕᵀPϕ)`, from the form of `P⁻¹` at `ρ - λPϕ` being nonnegative for
every `λ`; every point is attained at `ϑ = c + (t/√(ϕᵀPϕ)) Pϕ`, `e = tγ`, `|t| ≤ 1`.

## References

* [1] M. C. Campi, G. Calafiore and S. Garatti. "Interval predictor models: Identification and
      reliability". Automatica, 45(2):382-392, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- Cauchy-Schwarz in the inner products of `P⁻¹` and `P`
theorem aux_abs_dotProduct_le_weighted (P : Mat ℝ n n) (hP : P.PosDef) (ρ ϕ : Vec ℝ n) :
    |ρ ⬝ᵥ ϕ| ≤ Real.sqrt (ρ ⬝ᵥ (P⁻¹ *ᵥ ρ)) * Real.sqrt (ϕ ⬝ᵥ (P *ᵥ ϕ)) := by -- --- PROOF ---
  haveI : Invertible P := hP.isUnit.invertible
  have hPT : Pᵀ = P := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hP.isHermitian.eq
  have ha : 0 ≤ ρ ⬝ᵥ (P⁻¹ *ᵥ ρ) := by
    simpa using hP.inv.posSemidef.dotProduct_mulVec_nonneg ρ
  have hb : 0 ≤ ϕ ⬝ᵥ (P *ᵥ ϕ) := by
    simpa using hP.posSemidef.dotProduct_mulVec_nonneg ϕ
  -- the form of `P⁻¹` at `ρ - λ P ϕ`
  have hq : ∀ l : ℝ, 0 ≤ ρ ⬝ᵥ (P⁻¹ *ᵥ ρ) - 2 * l * (ρ ⬝ᵥ ϕ) + l ^ 2 * (ϕ ⬝ᵥ (P *ᵥ ϕ)) := by
    intro l
    have h0 := hP.inv.posSemidef.dotProduct_mulVec_nonneg (ρ - l • (P *ᵥ ϕ))
    simp only [star_trivial] at h0
    have h1 : P⁻¹ *ᵥ (P *ᵥ ϕ) = ϕ := by rw [mulVec_mulVec, inv_mul_of_invertible, one_mulVec]
    have h2 : (P *ᵥ ϕ) ⬝ᵥ (P⁻¹ *ᵥ ρ) = ϕ ⬝ᵥ ρ := by
      rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hPT, mulVec_mulVec,
        mul_inv_of_invertible, one_mulVec]
      exact dotProduct_comm _ _
    rw [mulVec_sub, mulVec_smul, h1] at h0
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, h2,
      dotProduct_comm ϕ ρ] at h0
    rw [dotProduct_comm (P *ᵥ ϕ) ϕ] at h0
    nlinarith [h0]
  rw [← Real.sqrt_mul ha, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · -- `ϕᵀPϕ = 0`: the form is linear in `λ`, so `ρᵀϕ = 0`
    by_contra hne
    push Not at hne
    have hρϕ : ρ ⬝ᵥ ϕ ≠ 0 := by
      intro h0; rw [h0] at hne; simp [← hb0] at hne
    have hl : 2 * ((ρ ⬝ᵥ (P⁻¹ *ᵥ ρ) + 1) / (2 * (ρ ⬝ᵥ ϕ))) * (ρ ⬝ᵥ ϕ) =
        ρ ⬝ᵥ (P⁻¹ *ᵥ ρ) + 1 := by field_simp
    have := hq ((ρ ⬝ᵥ (P⁻¹ *ᵥ ρ) + 1) / (2 * (ρ ⬝ᵥ ϕ)))
    rw [hl, ← hb0] at this
    linarith
  · have := hq ((ρ ⬝ᵥ ϕ) / (ϕ ⬝ᵥ (P *ᵥ ϕ)))
    field_simp at this
    nlinarith [this]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ipmEllipsoid_eq (c : Vec ℝ n) (P : Mat ℝ n n) (hP : P.PosDef) (γ : ℝ) (hγ : 0 ≤ γ)
    (ϕ : Vec ℝ n) :
    ipmEllipsoid c P γ ϕ = Set.Icc (c ⬝ᵥ ϕ - (Real.sqrt (ϕ ⬝ᵥ (P *ᵥ ϕ)) + γ))
      (c ⬝ᵥ ϕ + (Real.sqrt (ϕ ⬝ᵥ (P *ᵥ ϕ)) + γ)) := by -- --- PROOF ---
  haveI : Invertible P := hP.isUnit.invertible
  have hPT : Pᵀ = P := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hP.isHermitian.eq
  have hb : 0 ≤ ϕ ⬝ᵥ (P *ᵥ ϕ) := by
    simpa using hP.posSemidef.dotProduct_mulVec_nonneg ϕ
  ext y
  constructor
  · -- the enclosure: `|ρᵀϕ| ≤ √(ρᵀP⁻¹ρ)√(ϕᵀPϕ) ≤ √(ϕᵀPϕ)`
    rintro ⟨ϑ, e, hϑ, he, rfl⟩
    have hρ : |(ϑ - c) ⬝ᵥ ϕ| ≤ Real.sqrt (ϕ ⬝ᵥ (P *ᵥ ϕ)) := by
      refine (aux_abs_dotProduct_le_weighted P hP _ _).trans ?_
      calc Real.sqrt ((ϑ - c) ⬝ᵥ (P⁻¹ *ᵥ (ϑ - c))) * Real.sqrt (ϕ ⬝ᵥ (P *ᵥ ϕ))
          ≤ 1 * Real.sqrt (ϕ ⬝ᵥ (P *ᵥ ϕ)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
            calc _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hϑ
              _ = 1 := Real.sqrt_one
        _ = _ := one_mul _
    have hsplit : ϑ ⬝ᵥ ϕ = c ⬝ᵥ ϕ + (ϑ - c) ⬝ᵥ ϕ := by rw [sub_dotProduct]; ring
    rw [abs_le] at hρ he
    constructor <;> linarith
  · -- every point: `y = cᵀϕ + t(√(ϕᵀPϕ) + γ)` for some `t ∈ [-1, 1]`
    rintro ⟨h1, h2⟩
    set w := Real.sqrt (ϕ ⬝ᵥ (P *ᵥ ϕ)) + γ
    have hw : 0 ≤ w := by positivity
    rcases eq_or_lt_of_le hw with hw0 | hwpos
    · refine ⟨c, 0, by simp, by simpa using hγ, ?_⟩
      simp; linarith
    set t := (y - c ⬝ᵥ ϕ) / w
    have ht : |t| ≤ 1 := by
      rw [abs_le]; constructor
      · rw [le_div_iff₀ hwpos]; linarith
      · rw [div_le_iff₀ hwpos]; linarith
    have hyt : y = c ⬝ᵥ ϕ + t * w := by simp only [t]; field_simp; ring
    have hte : |t * γ| ≤ γ := by
      rw [abs_mul, abs_of_nonneg hγ]
      calc |t| * γ ≤ 1 * γ := mul_le_mul_of_nonneg_right ht hγ
        _ = γ := one_mul γ
    -- the regressor term reaches `t√(ϕᵀPϕ)` along `Pϕ`, the noise `tγ`
    rcases eq_or_lt_of_le hb with hb0 | hbpos
    · -- `ϕᵀPϕ = 0`: the noise alone
      refine ⟨c, t * γ, by simp, hte, ?_⟩
      have : w = γ := by simp [w, ← hb0]
      rw [hyt, this]
    · set s := Real.sqrt (ϕ ⬝ᵥ (P *ᵥ ϕ))
      have hs : 0 < s := Real.sqrt_pos.mpr hbpos
      have hss : ϕ ⬝ᵥ (P *ᵥ ϕ) = s ^ 2 := (Real.sq_sqrt hb).symm
      have hPϕ : (P *ᵥ ϕ) ⬝ᵥ ϕ = s ^ 2 := by rw [dotProduct_comm]; exact hss
      have h1 : P⁻¹ *ᵥ (P *ᵥ ϕ) = ϕ := by rw [mulVec_mulVec, inv_mul_of_invertible, one_mulVec]
      refine ⟨c + (t / s) • (P *ᵥ ϕ), t * γ, ?_, hte, ?_⟩
      · simp only [add_sub_cancel_left, mulVec_smul, h1, smul_dotProduct, dotProduct_smul,
          smul_eq_mul, hPϕ]
        field_simp
        have := abs_le.mp ht
        nlinarith
      · rw [hyt, add_dotProduct, smul_dotProduct, smul_eq_mul, hPϕ]
        simp only [w]
        field_simp
        ring

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
