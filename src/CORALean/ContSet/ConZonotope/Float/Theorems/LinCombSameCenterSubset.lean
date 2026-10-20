module

public import CORALean.ContSet.ConZonotope.Float.Operations.LinCombSameCenter
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Operations.MemStackRowsNominalIff
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecSingle
public import CORALean.ContSet.HPolytope.Float.Operations.MemUnitBoxIff
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLeft
public import CORALean.Global.Float.ToRealMatMulVec
public import CORALean.ContSet.HPolytope.Float.Theorems.MemHalfScaledLeft
public import CORALean.ContSet.HPolytope.Float.Theorems.MemHalfScaledRight

@[expose] public section

/-!
# `linCombSameCenter` is no larger than the hull

The nominal part of the hull of two constrained zonotopes at one center lies on the segments between
their nominal parts. A coefficient vector `(γ₁, γ₂, ν)` of the hull meets the first block's rows at
the weight `λ = (ν + 1) / 2` and the second's at `1 - λ`, so each block is a point of its own set
scaled by its weight: above zero by dividing through, at zero because the weighted unit box pins the
block to the origin. Both sets must be nonempty, as in `linComb_inner`, and both polytopes
slack-free: a slack is read once at every weight. The centers agree and the interpolation column is
zero, so the point is `λ(c + G₁β₁) + (1 - λ)(c + G₂β₂)`.

## Inputs
* `cZ₁` – first constrained zonotope
* `cZ₂` – second constrained zonotope

## Hypotheses
* `hc` – the two centers agree
* `hs₁` – first constraint slack free
* `hs₂` – second constraint slack free
* `hne₁` – first nominal set nonempty
* `hne₂` – second nominal set nonempty

## Conclusion
* the nominal hull lies within the hull of the nominal sets
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A block meeting a polytope's rows and the unit box's at weight `lam` is `lam` times a
coefficient vector of the polytope inside the unit box, the polytope being nonempty there. -/
theorem ConZonotope.aux_blockCoeff {k : ℕ} (P : HPolytope 𝕋 (Vec 𝕋 k))
    (hne : ∃ β : Vec ℝ k, (∀ j, |β j| ≤ 1) ∧ β ∈ P.nominal.construct) {γ : Vec ℝ k} {lam : ℝ}
    {Q : HPolytope 𝕋 (Vec 𝕋 k)} (hQ : Q = P.stackRows (HPolytope.unitBox 𝕋 k))
    (hl0 : 0 ≤ lam)
    (hA : ∀ i, (toRealMat Q.A *ᵥ γ) i ≤ lam * toReal (Q.b i))
    (hE : ∀ i, (toRealMat Q.Ae *ᵥ γ) i = lam * toReal (Q.be i)) : -- --- CONCL ---
    ∃ β : Vec ℝ k, (∀ j, |β j| ≤ 1) ∧ β ∈ P.nominal.construct ∧ lam • β = γ := by -- --- PROOF ---
  obtain rfl | hpos := hl0.eq_or_lt
  · -- zero weight: the unit-box rows pin the block to the origin
    obtain ⟨β, hβ, hP⟩ := hne
    refine ⟨β, hβ, hP, funext fun j => ?_⟩
    -- the two unit-box rows of coordinate `j`, at weight zero, bound it by `0` both ways
    subst hQ
    have hup := hA (Fin.natAdd P.m (Fin.castAdd k j))
    have hlo := hA (Fin.natAdd P.m (Fin.natAdd k j))
    simp only [HPolytope.stackRows, toRealMat_append_mulVec_natAdd, Fin.append_right,
      HPolytope.unitBox, HPolytope.mulVec_append_left, HPolytope.mulVec_single,
      toReal_one, toReal_neg, one_mul, neg_mul, zero_mul] at hup hlo
    simp only [Pi.smul_apply, zero_smul]
    linarith
  · -- positive weight: divide through, the rows then holding as stated
    refine ⟨lam⁻¹ • γ, ?_⟩
    -- the divided vector meets the rows at weight one, and the unit box
    have hmem : lam⁻¹ • γ ∈ Q.nominal.construct := by
      refine HPolytope.mem_nominal_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
      · -- the inequality rows scale by `lam⁻¹`
        rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
        refine le_add_of_le_of_nonneg ?_ (abs_nonneg _)
        calc lam⁻¹ * (toRealMat Q.A *ᵥ γ) i
            ≤ lam⁻¹ * (lam * toReal (Q.b i)) :=
              mul_le_mul_of_nonneg_left (hA i) (inv_nonneg.mpr hl0)
          _ = _ := by field_simp
      · rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hE i]
        refine le_trans (le_of_eq ?_) (abs_nonneg _)
        rw [abs_eq_zero, sub_eq_zero]
        field_simp
    rw [hQ] at hmem
    obtain ⟨hP, hbox⟩ := HPolytope.mem_stackRows_nominal_iff.mp hmem
    exact ⟨HPolytope.mem_unitBox_iff.mp ((HPolytope.mem_nominal_of_origin rfl).mpr hbox), hP,
      by rw [smul_smul, mul_inv_cancel₀ hpos.ne',
      one_smul]⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.linCombSameCenter_subset (cZ₁ cZ₂ : ConZonotope 𝕋 (Vec 𝕋 n))
    (hc : cZ₂.c = cZ₁.c) (hs₁ : cZ₁.P.IsSlackFree) (hs₂ : cZ₂.P.IsSlackFree)
    (hne₁ : (nominalSet cZ₁).Nonempty) (hne₂ : (nominalSet cZ₂).Nonempty) : -- --- CONCL ---
    nominalSet (cZ₁.linCombSameCenter cZ₂) ⊆
      Set.linComb (nominalSet cZ₁) (nominalSet cZ₂) := by -- --- PROOF ---
  intro x hx
  -- the nominal point, at its coefficients
  obtain ⟨β, hβ, hP, hval⟩ := ConZonotope.mem_nominalSet_iff.mp hx
  -- the coefficient vector in its three blocks
  set γ₁ : Vec ℝ cZ₁.h := fun j => β (Fin.castAdd 1 (Fin.castAdd cZ₂.h j)) with hγ₁
  set γ₂ : Vec ℝ cZ₂.h := fun j => β (Fin.castAdd 1 (Fin.natAdd cZ₁.h j)) with hγ₂
  set ν : ℝ := β (Fin.natAdd (cZ₁.h + cZ₂.h) 0) with hν
  have hβeq : β = Fin.append (Fin.append γ₁ γ₂) fun _ : Fin 1 => ν := by
    funext j
    refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
    · refine Fin.addCases (fun j'' => ?_) (fun j'' => ?_) j'
      · simp [hγ₁]
      · simp [hγ₂]
    · have : j' = 0 := Subsingleton.elim _ _
      subst this
      simp [hν]
  -- the three row groups of the hull's coefficient polytope
  have hP' : β ∈ (((cZ₁.P.stackRows (HPolytope.unitBox 𝕋 cZ₁.h)).halfScaledLeft
      cZ₂.h).stackRows (HPolytope.halfScaledRight cZ₁.h
        (cZ₂.P.stackRows (HPolytope.unitBox 𝕋 cZ₂.h)))).nominal.construct := hP
  obtain ⟨hL, hR⟩ := HPolytope.mem_stackRows_nominal_iff.mp hP'
  rw [hβeq] at hL hR
  replace hL := (HPolytope.mem_nominal_of_origin rfl).mpr hL
  replace hR := (HPolytope.mem_nominal_of_origin rfl).mpr hR
  obtain ⟨hA₁, hE₁⟩ := HPolytope.mem_halfScaledLeft hL
  obtain ⟨hA₂, hE₂⟩ := HPolytope.mem_halfScaledRight hR
  -- a slack-free block stays slack-free with its unit box stacked on, so the rows read exactly
  have hstack : ∀ {k : ℕ} (Q : HPolytope 𝕋 (Vec 𝕋 k)), Q.IsSlackFree →
      (Q.stackRows (HPolytope.unitBox 𝕋 k)).IsSlackFree := fun Q hs =>
    ⟨fun i => Fin.addCases (fun i => by simpa [HPolytope.stackRows] using hs.1 i)
      (fun i => by simp [HPolytope.stackRows, HPolytope.unitBox, toReal_zero]) i,
     fun i => Fin.addCases (fun i => by simpa [HPolytope.stackRows] using hs.2 i)
      (fun i => i.elim0) i⟩
  obtain ⟨hb₁, he₁⟩ := hstack cZ₁.P hs₁
  obtain ⟨hb₂, he₂⟩ := hstack cZ₂.P hs₂
  simp only [hb₁, hb₂, he₁, he₂, abs_zero, add_zero, abs_nonpos_iff, sub_eq_zero]
    at hA₁ hE₁ hA₂ hE₂
  -- the weight, and the second block's
  have hν1 : |ν| ≤ 1 := by
    have := hβ (Fin.natAdd (cZ₁.h + cZ₂.h) 0)
    exact this
  obtain ⟨hνl, hνu⟩ := abs_le.mp hν1
  set lam : ℝ := (ν + 1) / 2 with hlam
  have hl0 : 0 ≤ lam := by rw [hlam]; linarith
  have hl1 : lam ≤ 1 := by rw [hlam]; linarith
  have hw : (1 - ν) / 2 = 1 - lam := by rw [hlam]; ring
  rw [hw] at hA₂ hE₂
  -- each block is its weight times a coefficient vector of its own set
  obtain ⟨β₁, hβ₁, hP₁, hγ₁eq⟩ := ConZonotope.aux_blockCoeff cZ₁.P
    (by obtain ⟨y, hy⟩ := hne₁
        obtain ⟨b, hb, hbP, -⟩ := ConZonotope.mem_nominalSet_iff.mp hy
        exact ⟨b, hb, hbP⟩) rfl hl0 hA₁ hE₁
  obtain ⟨β₂, hβ₂, hP₂, hγ₂eq⟩ := ConZonotope.aux_blockCoeff cZ₂.P
    (by obtain ⟨y, hy⟩ := hne₂
        obtain ⟨b, hb, hbP, -⟩ := ConZonotope.mem_nominalSet_iff.mp hy
        exact ⟨b, hb, hbP⟩) rfl (by linarith) hA₂ hE₂
  refine ⟨fun i => toReal (cZ₁.c i) + ∑ j, toReal (cZ₁.G j i) * β₁ j,
    ConZonotope.mem_nominalSet_iff.mpr ⟨β₁, hβ₁, hP₁, fun _ => rfl⟩,
    fun i => toReal (cZ₂.c i) + ∑ j, toReal (cZ₂.G j i) * β₂ j,
    ConZonotope.mem_nominalSet_iff.mpr ⟨β₂, hβ₂, hP₂, fun _ => rfl⟩, lam, ⟨hl0, hl1⟩, ?_⟩
  funext i
  have hxi := hval i
  -- the value of the stored hull at the coefficients, in three blocks
  change x i = toReal (cZ₁.c i) + ∑ j : Fin (cZ₁.h + cZ₂.h + 1),
    toReal (Fin.append (Fin.append cZ₁.G cZ₂.G) (fun _ : Fin 1 => fun _ => (zero : 𝕋)) j i)
      * β j at hxi
  rw [hβeq, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one] at hxi
  simp only [Fin.append_left, Fin.append_right, toReal_zero, zero_mul, add_zero] at hxi
  -- the blocks, as their weights times the coefficients of their own sets
  have e₁ : ∑ j, toReal (cZ₁.G j i) * γ₁ j = lam * ∑ j, toReal (cZ₁.G j i) * β₁ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hγ₁eq]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have e₂ : ∑ j, toReal (cZ₂.G j i) * γ₂ j = (1 - lam) * ∑ j, toReal (cZ₂.G j i) * β₂ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hγ₂eq]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hci : toReal (cZ₂.c i) = toReal (cZ₁.c i) := by rw [hc]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hxi, e₁, e₂, hci]
  ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
