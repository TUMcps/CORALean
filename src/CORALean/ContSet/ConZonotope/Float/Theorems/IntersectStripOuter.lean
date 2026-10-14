module

public import CORALean.ContSet.ConZonotope.Float.Operations.IntersectStrip
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Operations.MemEqsIff
public import CORALean.ContSet.HPolytope.Float.Operations.MemIntersectionIff
public import CORALean.ContSet.HPolytope.Float.Operations.MemPadLeftIff
public import CORALean.ContSet.Interval.Float.Theorems.MinusOuter
public import CORALean.ContSet.Interval.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError

@[expose] public section

/-!
# The float `intersectStrip` encloses the intersection with the strip

A point `x = c + G ξ + e` of the set with `|C x - y| ≤ φ` gets the strip factors
`ν = (C x - y) / φ` (`0` on a slab of width `0`). The strip rows hold at `[ξ; ν]`: the image
`C x` is the float image's nominal point at `ξ` plus a point of its box, as in `conIntersect`.
The point is the new nominal point at `[ξ; ν]` plus the error the box holds: over ℝ,
`c' + (I - Λ C) G ξ + Λ φ ν = c + G ξ + Λ C e` exactly, because `C G ξ - φ ν = y - C c - C e`;
so `x` is that plus `e - Λ C e`, plus the rounding of the new centre and generators. For every
gain `Λ`; outer only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n s : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The exact image of `c + G ξ + e`, regrouped so the centre and each generator appear once. -/
theorem ConZonotope.aux_strip_regroup {h : ℕ} (M : Mat 𝕋 s n) (c : Vec 𝕋 n) (G : Fin h → Vec 𝕋 n)
    (β : Vec ℝ h) (e : Vec ℝ n) {x : Vec ℝ n}
    (hx : ∀ k, x k = toReal (c k) + ∑ j, toReal (G j k) * β j + e k) (i : Fin s) :
    (toRealMat M *ᵥ x) i = (∑ k, toReal (M i k) * toReal (c k))
      + ∑ j, (∑ k, toReal (M i k) * toReal (G j k)) * β j
      + (toRealMat M *ᵥ e) i := by -- --- PROOF ---
  show ∑ k, toReal (M i k) * x k = _ + _ + ∑ k, toReal (M i k) * e k
  calc ∑ k, toReal (M i k) * x k
      = ∑ k, (toReal (M i k) * toReal (c k)
              + ∑ j, toReal (M i k) * toReal (G j k) * β j + toReal (M i k) * e k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hx k, mul_add, mul_add, Finset.mul_sum]
        exact congrArg₂ _ (congrArg _ (Finset.sum_congr rfl fun j _ => by ring)) rfl
    _ = (∑ k, toReal (M i k) * toReal (c k))
        + ∑ k, ∑ j, toReal (M i k) * toReal (G j k) * β j
        + ∑ k, toReal (M i k) * e k := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = _ := by
        rw [Finset.sum_comm (f := fun k j => toReal (M i k) * toReal (G j k) * β j)]
        exact congrArg₂ _ (congrArg _ (Finset.sum_congr rfl fun j _ =>
          (Finset.sum_mul _ _ _).symm)) rfl

/-- A product rounded down is off by at most the rounded gap to the one rounded up. -/
theorem ConZonotope.aux_strip_mulDown_gap (a r : 𝕋) :
    |toReal a * toReal r - toReal (mulDown a r)|
      ≤ toReal (subUp (mulUp a r) (mulDown a r)) := by -- --- PROOF ---
  have h1 := mulDown_le_mul a r
  have h2 := mul_le_mulUp a r
  have h3 := sub_le_subUp (mulUp a r) (mulDown a r)
  rw [abs_le]
  constructor <;> linarith


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.intersectStrip_outer (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (C : Mat 𝕋 s n)
    (φ y : Vec 𝕋 s)
    (Λ : Mat 𝕋 n s) :
    cZ.construct ∩ {x | ∀ k, |(toRealMat C *ᵥ x) k - toReal (y k)| ≤ toReal (φ k)}
      ⊆ (cZ.intersectStrip C φ y Λ).construct := by -- --- PROOF ---
  rintro x ⟨⟨y₁, hy₁', e, he, hx⟩, hstrip⟩
  obtain ⟨ξ, hξ, hP, hy₁⟩ := ConZonotope.mem_nominalSet_iff.mp hy₁'
  have hxk : ∀ k, x k = toReal (cZ.c k) + ∑ j, toReal (cZ.G j k) * ξ j + e k := by
    intro k
    have h : y₁ k + e k = x k := congrFun hx k
    rw [← h, hy₁ k]
  set W := Zonotope.mtimes C ⟨cZ.h, cZ.c, cZ.G, cZ.I_error⟩ with hW
  -- the exact entries of `C G`
  set CG : Mat ℝ s cZ.h := fun k j => ∑ l, toReal (C k l) * toReal (cZ.G j l) with hCG
  have hCx : ∀ k, (toRealMat C *ᵥ x) k = (∑ l, toReal (C k l) * toReal (cZ.c l))
      + ∑ j, CG k j * ξ j + (toRealMat C *ᵥ e) k :=
    ConZonotope.aux_strip_regroup C cZ.c cZ.G ξ e hxk
  -- the strip factors
  set ν : Vec ℝ s := fun k =>
    if toReal (φ k) = 0 then 0 else ((toRealMat C *ᵥ x) k - toReal (y k)) / toReal (φ k) with hνdef
  have hν : ∀ k, |ν k| ≤ 1 := by
    intro k
    simp only [hνdef]
    split_ifs with h0
    · simp
    · have hpos : 0 < toReal (φ k) :=
        lt_of_le_of_ne (le_trans (abs_nonneg _) (hstrip k)) (Ne.symm h0)
      rw [abs_div, abs_of_pos hpos, div_le_one hpos]
      exact hstrip k
  have hνeq : ∀ k, (toRealMat C *ᵥ x) k - toReal (y k) = toReal (φ k) * ν k := by
    intro k
    simp only [hνdef]
    split_ifs with h0
    · have := hstrip k
      rw [h0] at this
      rw [h0, zero_mul]
      exact abs_nonpos_iff.mp this
    · field_simp
  -- the image's nominal point at `ξ`, and what is left of `C x`, inside the image's box
  set eW : Vec ℝ s := fun k =>
    (toRealMat C *ᵥ x) k - (toReal (W.c k) + ∑ j, toReal (W.G j k) * ξ j) with heW
  have heWmem : eW ∈ W.I_error.construct := by
    have hgen : ∀ k j, |CG k j - toReal (mulVecDown C (cZ.G j) k)|
        ≤ toReal (matMulDiff C (fun i j => cZ.G j i) k j) := by
      intro k j
      have hlo : toReal (mulVecDown C (cZ.G j) k) ≤ CG k j := dotDown_le (C k) (fun l => cZ.G j l)
      have hhi : CG k j ≤ toReal (mulVecUp C (cZ.G j) k) := le_dotUp (C k) (fun l => cZ.G j l)
      have hgap := sub_le_subUp (mulVecUp C (cZ.G j) k) (mulVecDown C (cZ.G j) k)
      change _ ≤ toReal (subUp (mulVecUp C (cZ.G j) k) (mulVecDown C (cZ.G j) k))
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    -- the box's image, then the centre's and the generators' rounding
    refine Interval.plus_outer _ _
        ⟨toRealMat C *ᵥ e, Interval.mtimes_outer C cZ.I_error ⟨e, he, rfl⟩,
      _, Interval.plus_outer _ _
        ⟨_, Interval.sub_mem_residual (stored := mulVecDown C cZ.c)
            (fun k => ⟨dotDown_le (C k) cZ.c, le_dotUp (C k) cZ.c⟩),
         _, Zonotope.mem_generatorError hgen hξ, rfl⟩, ?_⟩
    funext k
    have hsum : (∑ j, toReal (mulVecDown C (cZ.G j) k) * ξ j)
        + (∑ j, (CG k j - toReal (mulVecDown C (cZ.G j) k)) * ξ j) = ∑ j, CG k j * ξ j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    show (toRealMat C *ᵥ e) k
        + ((∑ l, toReal (C k l) * toReal (cZ.c l) - toReal (mulVecDown C cZ.c k))
          + ∑ j, (CG k j - toReal (mulVecDown C (cZ.G j) k)) * ξ j)
      = (toRealMat C *ᵥ x) k - (toReal (mulVecDown C cZ.c k)
          + ∑ j, toReal (mulVecDown C (cZ.G j) k) * ξ j)
    rw [hCx k]
    linarith [hsum]
  -- the stored data of the result, named as in the definition
  set w : Interval (Vec 𝕋 s) :=
    ⟨fun k => subDown (y k) (dotUp (C k) cZ.c), fun k => subUp (y k) (dotDown (C k) cZ.c)⟩
    with hwdef
  set shift := Interval.mtimes Λ w with hshiftdef
  set cLo : Vec 𝕋 n := fun i => addDown (cZ.c i) (shift.inf i) with hcLo
  set cHi : Vec 𝕋 n := fun i => addUp (cZ.c i) (shift.sup i) with hcHi
  set LCG : Fin cZ.h → Interval (Vec 𝕋 n) := fun j =>
    Interval.mtimes Λ ⟨mulVecDown C (cZ.G j), mulVecUp C (cZ.G j)⟩ with hLCG
  set G₁ : Fin cZ.h → Vec 𝕋 n := fun j i => subDown (cZ.G j i) ((LCG j).sup i) with hG₁
  set gap₁ : Mat 𝕋 n cZ.h := fun i j => subUp (subUp (cZ.G j i) ((LCG j).inf i)) (G₁ j i)
    with hgap₁
  set G₂ : Fin s → Vec 𝕋 n := fun k i => mulDown (Λ i k) (φ k) with hG₂
  set gap₂ : Mat 𝕋 n s := fun i k => subUp (mulUp (Λ i k) (φ k)) (G₂ k i) with hgap₂
  -- `y - C c` and the columns of `C G`, inside their boxes, and their images under `Λ`
  set wR : Vec ℝ s := fun k => toReal (y k) - ∑ l, toReal (C k l) * toReal (cZ.c l) with hwR
  have hw : wR ∈ w.construct := fun k => by
    have h1 := dotDown_le (C k) cZ.c
    have h2 := le_dotUp (C k) cZ.c
    have h3 := subDown_le_sub (y k) (dotUp (C k) cZ.c)
    have h4 := sub_le_subUp (y k) (dotDown (C k) cZ.c)
    show toReal (subDown (y k) (dotUp (C k) cZ.c)) ≤ wR k
      ∧ wR k ≤ toReal (subUp (y k) (dotDown (C k) cZ.c))
    simp only [hwR]
    constructor <;> linarith
  have hshift := Interval.mtimes_outer Λ w ⟨wR, hw, rfl⟩
  have hcol : ∀ j, (toRealMat Λ *ᵥ fun k => CG k j) ∈ (LCG j).construct := fun j =>
    Interval.mtimes_outer Λ _ ⟨fun k => CG k j, fun k =>
      ⟨dotDown_le (C k) (fun l => cZ.G j l), le_dotUp (C k) (fun l => cZ.G j l)⟩, rfl⟩
  -- the first generator block's rounding
  have hgen₁ : ∀ i j, |(toReal (cZ.G j i) - (toRealMat Λ *ᵥ fun k => CG k j) i)
      - toReal (G₁ j i)| ≤ toReal (gap₁ i j) := by
    intro i j
    have hb : toReal ((LCG j).inf i) ≤ (toRealMat Λ *ᵥ fun k => CG k j) i
        ∧ (toRealMat Λ *ᵥ fun k => CG k j) i ≤ toReal ((LCG j).sup i) := hcol j i
    have h1 := subDown_le_sub (cZ.G j i) ((LCG j).sup i)
    have h2 := sub_le_subUp (cZ.G j i) ((LCG j).inf i)
    have h3 := sub_le_subUp (subUp (cZ.G j i) ((LCG j).inf i)) (G₁ j i)
    rw [abs_le]
    simp only [hgap₁, hG₁] at h3 ⊢
    constructor <;> linarith
  have hgen₂ : ∀ i k, |toReal (Λ i k) * toReal (φ k) - toReal (G₂ k i)| ≤ toReal (gap₂ i k) :=
    fun i k => ConZonotope.aux_strip_mulDown_gap _ _
  -- the new centre's rounding
  have hcen : ∀ i, toReal (cLo i) ≤ toReal (cZ.c i) + (toRealMat Λ *ᵥ wR) i
      ∧ toReal (cZ.c i) + (toRealMat Λ *ᵥ wR) i ≤ toReal (cHi i) := by
    intro i
    have hb : toReal (shift.inf i) ≤ (toRealMat Λ *ᵥ wR) i
        ∧ (toRealMat Λ *ᵥ wR) i ≤ toReal (shift.sup i) := hshift i
    have h1 := addDown_le_add (cZ.c i) (shift.inf i)
    have h2 := add_le_addUp (cZ.c i) (shift.sup i)
    exact ⟨by simp only [hcLo]; linarith, by simp only [hcHi]; linarith⟩
  -- `e - Λ C e`, inside the box of the two interval images
  have heΛ : e - toRealMat Λ *ᵥ (toRealMat C *ᵥ e)
      ∈ (cZ.I_error.minus (Interval.mtimes Λ (Interval.mtimes C cZ.I_error))).construct :=
    Interval.minus_outer _ _ ⟨e, he, _, Interval.mtimes_outer Λ _
      ⟨_, Interval.mtimes_outer C cZ.I_error ⟨e, he, rfl⟩, rfl⟩, rfl⟩
  -- the strip rows, and the old ones on the first block
  have hPnew : Fin.append ξ ν ∈ ((cZ.P.padLeft s).intersection (HPolytope.eqs
      (fun k => Fin.append (fun j => W.G j k) fun l => if l = k then neg (φ k) else zero)
      ⟨fun k => subDown (subDown (y k) (W.c k)) (W.I_error.sup k),
       fun k => subUp (subUp (y k) (W.c k)) (W.I_error.inf k)⟩)).construct := by
    refine HPolytope.mem_intersection_iff.mpr ⟨HPolytope.mem_padLeft_iff.mpr ?_,
      HPolytope.mem_eqs_iff.mpr fun k => ?_⟩
    · rw [blockLeft_append]; exact hP
    · have hrow : (toRealMat (fun k => Fin.append (fun j => W.G j k) fun l =>
            if l = k then neg (φ k) else zero) *ᵥ Fin.append ξ ν) k
          = ∑ j, toReal (W.G j k) * ξ j - toReal (φ k) * ν k := by
        simp only [mulVec, dotProduct, toRealMat, Fin.sum_univ_add, Fin.append_left,
          Fin.append_right]
        rw [Finset.sum_eq_single k (fun l _ hl => by rw [if_neg hl, toReal_zero, zero_mul])
          (fun h => absurd (Finset.mem_univ k) h), if_pos rfl, toReal_neg]
        ring
      -- the row is `y - W.c - eW`, and `eW` is inside the image's box
      have hb : toReal (W.I_error.inf k) ≤ eW k ∧ eW k ≤ toReal (W.I_error.sup k) := heWmem k
      have he' := hνeq k
      have hk : ∑ j, toReal (W.G j k) * ξ j - toReal (φ k) * ν k
          = toReal (y k) - toReal (W.c k) - eW k := by
        simp only [heW]; linarith
      show toReal (subDown (subDown (y k) (W.c k)) (W.I_error.sup k))
          ≤ (toRealMat (fun k => Fin.append (fun j => W.G j k) fun l => if l = k then neg (φ k)
            else zero) *ᵥ Fin.append ξ ν) k
        ∧ (toRealMat (fun k => Fin.append (fun j => W.G j k) fun l => if l = k then neg (φ k)
            else zero) *ᵥ Fin.append ξ ν) k ≤ toReal (subUp (subUp (y k) (W.c k)) (W.I_error.inf k))
      rw [hrow, hk]
      have h1 := subDown_le_sub (y k) (W.c k)
      have h2 := subDown_le_sub (subDown (y k) (W.c k)) (W.I_error.sup k)
      have h3 := sub_le_subUp (y k) (W.c k)
      have h4 := sub_le_subUp (subUp (y k) (W.c k)) (W.I_error.inf k)
      exact ⟨by linarith, by linarith⟩
  -- the bracket the gain multiplies is zero: the strip rows at `x`
  have hbr : ∀ k, wR k - ∑ j, CG k j * ξ j + toReal (φ k) * ν k
      - (toRealMat C *ᵥ e) k = 0 := by
    intro k
    have h1 := hCx k
    have h2 := hνeq k
    simp only [hwR]
    linarith
  -- so the gain's whole contribution vanishes
  have hkey : ∀ i, (toRealMat Λ *ᵥ wR) i - ∑ j, (toRealMat Λ *ᵥ fun k => CG k j) i * ξ j
      + ∑ k, toReal (Λ i k) * toReal (φ k) * ν k
      - (toRealMat Λ *ᵥ (toRealMat C *ᵥ e)) i = 0 := by
    intro i
    have hexp : (toRealMat Λ *ᵥ wR) i - ∑ j, (toRealMat Λ *ᵥ fun k => CG k j) i * ξ j
        + ∑ k, toReal (Λ i k) * toReal (φ k) * ν k
        - (toRealMat Λ *ᵥ (toRealMat C *ᵥ e)) i
        = ∑ k, toReal (Λ i k) * (wR k - ∑ j, CG k j * ξ j + toReal (φ k) * ν k
          - (toRealMat C *ᵥ e) k) := by
      simp only [mulVec, dotProduct, toRealMat, Finset.sum_mul]
      rw [Finset.sum_comm (f := fun j k => toReal (Λ i k) * CG k j * ξ j)]
      simp only [mul_sub, mul_add, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by
        simp only [mul_assoc]
    rw [hexp]
    exact Finset.sum_eq_zero fun k _ => by rw [hbr k, mul_zero]
  -- the witness: the new nominal point at `[ξ; ν]`, the error split four ways
  refine ⟨fun i => toReal (cLo i) + ∑ j : Fin (cZ.h + s),
      toReal (Fin.append G₁ G₂ j i) * Fin.append ξ ν j,
    ConZonotope.mem_nominalSet_iff.mpr ⟨Fin.append ξ ν, ?_, hPnew, fun _ => rfl⟩,
    _, Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _ ⟨_, Interval.plus_outer _ _
      ⟨_, heΛ, _, Interval.sub_mem_residual (stored := cLo) hcen, rfl⟩,
      _, Zonotope.mem_generatorError hgen₁ hξ, rfl⟩,
      _, Zonotope.mem_generatorError hgen₂ hν, rfl⟩, ?_⟩
  · refine Fin.addCases (fun j => ?_) fun k => ?_
    · rw [Fin.append_left]; exact hξ j
    · rw [Fin.append_right]; exact hν k
  · -- the point: the new nominal point plus `e - Λ C e` and the roundings
    funext i
    have hk := hkey i
    have hxi := hxk i
    simp only [Pi.add_apply, Pi.sub_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    have hM : ∑ j, (toReal (cZ.G j i) - (toRealMat Λ *ᵥ fun k => CG k j) i) * ξ j
        = ∑ j, toReal (cZ.G j i) * ξ j
          - ∑ j, (toRealMat Λ *ᵥ fun k => CG k j) i * ξ j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    -- each stored block plus its rounding is the exact block
    have hs1 : ∑ j, toReal (G₁ j i) * ξ j
        + ∑ j, ((toReal (cZ.G j i) - (toRealMat Λ *ᵥ fun k => CG k j) i)
          - toReal (G₁ j i)) * ξ j
        = ∑ j, (toReal (cZ.G j i) - (toRealMat Λ *ᵥ fun k => CG k j) i) * ξ j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hs2 : ∑ k, toReal (G₂ k i) * ν k
        + ∑ k, (toReal (Λ i k) * toReal (φ k) - toReal (G₂ k i)) * ν k
        = ∑ k, toReal (Λ i k) * toReal (φ k) * ν k := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hxi]
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
