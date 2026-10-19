module

public import CORALean.ContSet.ConZonotope.Real.Operations.IntersectStrip
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.ConZonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# `ConZonotope.intersectStrip` is exactly the intersection with the strip

[1, Lemma 2] at one strip.

For every gain `Λ`, not only the optimal ones: on the equality rows the factor of `Λ` vanishes,
`x₀ + Λ (y - C x₀ + φ ν) = x₀`, so the new representation names the same points as the old one
whose image lies in the strip (CORA's `aux_conZonotopeFromLambda`). The strip's widths are
nonnegative (`0 ≤ φ`); with a negative width the strip `|C x - y| ≤ φ` is empty and the new factor
`ν ∈ [-1, 1]` would still reach points.

## References

* [1] A. Alanwar, V. Gaßmann, X. He, H. Said, H. Sandberg, K. H. Johansson and M. Althoff.
      "Privacy-Preserving Set-Based Estimation Using Partially Homomorphic Encryption".
      European Journal of Control, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n s : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem ConZonotope.aux_value_intersectStrip (cZ : ConZonotope (Vec ℝ n)) (C : Mat ℝ s n)
    (φ y : Vec ℝ s) (Λ : Mat ℝ n s) (β : Vec ℝ (cZ.h + s)) : -- --- CONCL ---
    (cZ.intersectStrip C φ y Λ).c
        + ∑ j : Fin (cZ.h + s), β j • (cZ.intersectStrip C φ y Λ).G j
      = (cZ.c + ∑ j, β (Fin.castAdd s j) • cZ.G j)
        + Λ *ᵥ (y - C *ᵥ (cZ.c + ∑ j, β (Fin.castAdd s j) • cZ.G j)
                + fun i => φ i * β (Fin.natAdd cZ.h i)) := by -- --- PROOF ---
  dsimp only [ConZonotope.intersectStrip]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have h1 : ∑ j, β (Fin.castAdd s j) • ((1 - Λ * C) *ᵥ cZ.G j)
      = (∑ j, β (Fin.castAdd s j) • cZ.G j)
        - Λ *ᵥ (C *ᵥ ∑ j, β (Fin.castAdd s j) • cZ.G j) := by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, smul_sub,
      Finset.sum_sub_distrib, Matrix.mulVec_sum, Matrix.mulVec_smul]
  have h2 : ∑ i, β (Fin.natAdd cZ.h i) • (φ i • fun k => Λ k i)
      = Λ *ᵥ fun i => φ i * β (Fin.natAdd cZ.h i) := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub]
  abel


/-- `aux_value_intersectStrip` at the coefficient type `construct` uses. -/
theorem ConZonotope.aux_value_intersectStrip' (cZ : ConZonotope (Vec ℝ n)) (C : Mat ℝ s n)
    (φ y : Vec ℝ s) (Λ : Mat ℝ n s) (β : Vec ℝ (cZ.intersectStrip C φ y Λ).h) : -- --- CONCL ---
    (cZ.intersectStrip C φ y Λ).c
        + ∑ j : Fin (cZ.intersectStrip C φ y Λ).h, β j • (cZ.intersectStrip C φ y Λ).G j
      = (cZ.c + ∑ j, β (Fin.castAdd s j) • cZ.G j)
        + Λ *ᵥ (y - C *ᵥ (cZ.c + ∑ j, β (Fin.castAdd s j) • cZ.G j)
                + fun i => φ i * β (Fin.natAdd cZ.h i)) :=
  ConZonotope.aux_value_intersectStrip cZ C φ y Λ β

theorem ConZonotope.aux_row_intersectStrip (cZ : ConZonotope (Vec ℝ n)) (C : Mat ℝ s n)
    (φ : Vec ℝ s) (β : Vec ℝ (cZ.h + s)) (i : Fin s) : -- --- CONCL ---
    (cZ.stripMat C φ *ᵥ β) i
      = (C *ᵥ ∑ j, β (Fin.castAdd s j) • cZ.G j) i
        - φ i * β (Fin.natAdd cZ.h i) := by -- --- PROOF ---
  show ∑ j : Fin (cZ.h + s), cZ.stripMat C φ i j * β j = _
  rw [Fin.sum_univ_add]
  simp only [ConZonotope.stripMat, Fin.append_left, Fin.append_right, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.mulVec_sum, Matrix.mulVec_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [neg_mul, ← sub_eq_add_neg]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem ConZonotope.aux_mulVec_value (cZ : ConZonotope (Vec ℝ n)) (C : Mat ℝ s n)
    (β : Vec ℝ (cZ.h + s)) (i : Fin s) :
    (C *ᵥ (cZ.c + ∑ j, β (Fin.castAdd s j) • cZ.G j)) i
      = (C *ᵥ cZ.c) i + (C *ᵥ ∑ j, β (Fin.castAdd s j) • cZ.G j) i := by
  rw [Matrix.mulVec_add]; rfl

/-- The row condition says exactly that the gain's argument vanishes. -/
theorem ConZonotope.aux_mem_intersectStrip_P_iff (cZ : ConZonotope (Vec ℝ n)) (C : Mat ℝ s n)
    (φ y : Vec ℝ s) (Λ : Mat ℝ n s) (β : Vec ℝ (cZ.intersectStrip C φ y Λ).h) : -- --- CONCL ---
    β ∈ (cZ.intersectStrip C φ y Λ).P.construct ↔
      blockLeft cZ.h s β ∈ cZ.P.construct
        ∧ ∀ i, (y - C *ᵥ (cZ.c + ∑ j, β (Fin.castAdd s j) • cZ.G j)
                  + fun i => φ i * β (Fin.natAdd cZ.h i)) i = 0 := by -- --- PROOF ---
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := HPolytope.mem_intersection_iff.mp h
    refine ⟨h1, fun i => ?_⟩
    have := HPolytope.mem_eqs_iff.mp h2 i
    rw [ConZonotope.aux_row_intersectStrip] at this
    simp only [Pi.sub_apply] at this
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [ConZonotope.aux_mulVec_value]
    linarith
  · rintro ⟨h1, h2⟩
    refine HPolytope.mem_intersection_iff.mpr ⟨h1, HPolytope.mem_eqs_iff.mpr fun i => ?_⟩
    have := h2 i
    rw [ConZonotope.aux_row_intersectStrip]
    simp only [Pi.add_apply, Pi.sub_apply] at this
    rw [ConZonotope.aux_mulVec_value] at this
    simp only [Pi.sub_apply]
    linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.intersectStrip_exact (cZ : ConZonotope (Vec ℝ n)) (C : Mat ℝ s n)
    (φ y : Vec ℝ s) (Λ : Mat ℝ n s) (hφ : ∀ i, 0 ≤ φ i) :
    (cZ.intersectStrip C φ y Λ).construct
      = cZ.construct ∩ {x | ∀ i, |(C *ᵥ x) i - y i| ≤ φ i} := by -- --- PROOF ---
  ext x
  constructor
  · -- the rows make the gain's argument vanish, so the point is the old one
    rintro ⟨β, hβ, hP, hx⟩
    obtain ⟨hP₁, hr⟩ := (ConZonotope.aux_mem_intersectStrip_P_iff cZ C φ y Λ β).mp hP
    have hr' : (y - C *ᵥ (cZ.c + ∑ j, β (Fin.castAdd s j) • cZ.G j)
                  + fun i => φ i * β (Fin.natAdd cZ.h i)) = 0 := funext hr
    have hx₀ : x = cZ.c + ∑ j, β (Fin.castAdd s j) • cZ.G j := by
      rw [hx, ConZonotope.aux_value_intersectStrip', hr', Matrix.mulVec_zero, add_zero]
    refine ⟨⟨fun j => β (Fin.castAdd s j), fun j => hβ _, hP₁, hx₀⟩, fun i => ?_⟩
    -- the new factor `ν` carries the residue, and `|ν| ≤ 1` bounds it by the width
    have h := hr i
    simp only [Pi.add_apply, Pi.sub_apply] at h
    rw [← hx₀] at h
    have hν := hβ (Fin.natAdd cZ.h i)
    have : (C *ᵥ x) i - y i = φ i * β (Fin.natAdd cZ.h i) := by linarith
    rw [this, abs_mul, abs_of_nonneg (hφ i)]
    calc φ i * |β (Fin.natAdd cZ.h i)| ≤ φ i * 1 := mul_le_mul_of_nonneg_left hν (hφ i)
      _ = φ i := mul_one _
  · rintro ⟨⟨β₁, hβ₁, hP₁, hx⟩, hstrip⟩
    -- the new factor of slab `i` is the normalised residue `(C x - y)ᵢ / φᵢ`
    let ν : Vec ℝ s := fun i => if φ i = 0 then 0 else ((C *ᵥ x) i - y i) / φ i
    -- at width `0` the residue is `0`, else it is `φ ν`
    have hν : ∀ i, φ i * ν i = (C *ᵥ x) i - y i := by
      intro i
      by_cases h0 : φ i = 0
      · have := hstrip i
        rw [h0] at this
        have := abs_le.mp this
        simp only [ν, h0, if_true, mul_zero]
        linarith [this.1, this.2]
      · simp only [ν, h0, if_false]
        field_simp
    -- the strip bounds the residue by the width
    have hνle : ∀ i, |ν i| ≤ 1 := by
      intro i
      by_cases h0 : φ i = 0
      · simp [ν, h0]
      · have hpos : 0 < φ i := lt_of_le_of_ne (hφ i) (Ne.symm h0)
        simp only [ν, h0, if_false]
        rw [abs_div, abs_of_pos hpos, div_le_one hpos]
        exact hstrip i
    let β : Vec ℝ (cZ.intersectStrip C φ y Λ).h := Fin.append β₁ ν
    -- the first block of `β` is the point's own coefficient vector
    have hxβ : x = cZ.c + ∑ j, β (Fin.castAdd s j) • cZ.G j := by
      have : ∀ j, β (Fin.castAdd s j) = β₁ j := fun j => by simp [β]
      simp only [this]; exact hx
    -- the old factors and the new ones, side by side
    refine ⟨β, ?_, ?_, ?_⟩
    · refine Fin.addCases (fun l => ?_) fun l => ?_
      · simp only [β, Fin.append_left]; exact hβ₁ l
      · simp only [β, Fin.append_right]; exact hνle l
    · refine (ConZonotope.aux_mem_intersectStrip_P_iff cZ C φ y Λ β).mpr ⟨?_, fun i => ?_⟩
      · have : blockLeft cZ.h s β = β₁ := blockLeft_append β₁ ν
        rw [this]; exact hP₁
      · simp only [Pi.add_apply, Pi.sub_apply]
        have := hν i
        have e : β (Fin.natAdd cZ.h i) = ν i := by simp [β]
        rw [e, ← hxβ]
        linarith
    · -- the gain's argument vanishes at this `β`, so the value is the point `x`
      have hr : (y - C *ᵥ (cZ.c + ∑ j, β (Fin.castAdd s j) • cZ.G j)
                  + fun i => φ i * β (Fin.natAdd cZ.h i)) = 0 := by
        funext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
        have e : β (Fin.natAdd cZ.h i) = ν i := by simp [β]
        rw [e, hν i, ← hxβ]
        ring
      rw [ConZonotope.aux_value_intersectStrip', hr, Matrix.mulVec_zero, add_zero, hxβ.symm]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
