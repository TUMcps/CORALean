module

public import CORALean.ContSet.ConZonotope.Float.Operations.QuadMap
public import CORALean.ContSet.ConZonotope.Float.Theorems.AbsorbRoundingNominal
public import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapDep
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapCDown
public import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapCUp
public import CORALean.ContSet.ConZonotope.Float.Operations.QuadBilDown
public import CORALean.ContSet.ConZonotope.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadDownLe
public import CORALean.ContSet.PolyZonotope.Float.Theorems.LeQuadUp
public import CORALean.ContSet.ConZonotope.Real.Operations.QuadMap
public import CORALean.ContSet.ConZonotope.Float.Operations.QuadMapGDiff
public import CORALean.ContSet.ConZonotope.Real.Theorems.QuadMapOuter
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.MemPadLeftNominalIff
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemResidual
public import CORALean.ContSet.Zonotope.Float.Theorems.MemGeneratorError

@[expose] public section

/-!
# `ConZonotope.quadMap` over-approximates the quadratic map, on the factors

Every point of the operand, box included, is a point of the nominal set of `absorbRounding`
(`absorbRounding_nominal`), whose quadratic image is held by `quadMapDep`
(`aux_quadMapDep_nominal`). The result keeps the operand's constraints on the first block of
coefficients and gives the squares and the products none, so it is an outer approximation: it
contains the image, and need not equal it. Unlike `Zonotope.quadMap_outer` the guarantee is about
the constrained set, not a zonotope's.

## Inputs
* `Q` – quadratic form matrices
* `cZ` – float constrained zonotope

## Hypotheses
* none

## Conclusion
* the quadratic image is contained in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- The two roundings bracket the bilinear form. -/
private theorem ConZonotope.aux_quadBil_bracket (Q : Mat 𝕋 n n) (u v : Vec 𝕋 n) : -- --- CONCL ---
    toReal (ConZonotope.quadBilDown Q u v)
        ≤ toRealVec u ⬝ᵥ (toRealMat Q *ᵥ toRealVec v)
      ∧ toRealVec u ⬝ᵥ (toRealMat Q *ᵥ toRealVec v)
        ≤ toReal (ConZonotope.quadBilUp Q u v) := by -- --- PROOF ---
  -- each entry of `Q *ᵥ v` between its two directed dot products
  have hw : ∀ r, toReal (mulVecDown Q v r) ≤ (toRealMat Q *ᵥ toRealVec v) r
      ∧ (toRealMat Q *ᵥ toRealVec v) r ≤ toReal (mulVecUp Q v r) := fun r =>
    ⟨dotDown_le (Q r) v, le_dotUp (Q r) v⟩
  exact ⟨PolyZonotope.quadDown_le hw, PolyZonotope.le_quadUp hw⟩

end


section
open Pointwise

/-- The exact layer's generators on the read-back operand, at this layer's index type. -/
private noncomputable def ConZonotope.aux_quadMapGReal (Q : Fin m → Mat 𝕋 n n)
    (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    Fin m → Fin (cZ.h + cZ.h + cZ.h * cZ.h) → ℝ :=
  fun i l => Fin.append
    (Fin.append
      (fun j i => toRealVec cZ.c ⬝ᵥ (toRealMat (Q i) *ᵥ toRealVec (cZ.G j))
        + (toRealVec (cZ.G j)) ⬝ᵥ (toRealMat (Q i) *ᵥ toRealVec cZ.c))
      (fun j i => (1 / 2) * (toRealVec (cZ.G j)) ⬝ᵥ
        (toRealMat (Q i) *ᵥ toRealVec (cZ.G j))))
    (fun l i =>
      if (finProdFinEquiv.symm l).1 < (finProdFinEquiv.symm l).2
      then (toRealVec (cZ.G (finProdFinEquiv.symm l).1)) ⬝ᵥ
          (toRealMat (Q i) *ᵥ toRealVec (cZ.G (finProdFinEquiv.symm l).2))
        + (toRealVec (cZ.G (finProdFinEquiv.symm l).2)) ⬝ᵥ
          (toRealMat (Q i) *ᵥ toRealVec (cZ.G (finProdFinEquiv.symm l).1))
      else 0) l i


/-- The exact generator lies between the two stored roundings. -/
private theorem ConZonotope.aux_quadMapG_between (Q : Fin m → Mat 𝕋 n n)
    (cZ : ConZonotope 𝕋 (Vec 𝕋 n))
    (i : Fin m) (l : Fin (cZ.h + cZ.h + cZ.h * cZ.h)) : -- --- CONCL ---
    toReal (ConZonotope.quadMapGDown Q cZ i l) ≤ ConZonotope.aux_quadMapGReal Q cZ i l
      ∧ ConZonotope.aux_quadMapGReal Q cZ i l
        ≤ toReal (ConZonotope.quadMapGUp Q cZ i l) := by -- --- PROOF ---
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) l
    · -- the linear generator, two bilinear forms added
      obtain ⟨a1, a2⟩ := ConZonotope.aux_quadBil_bracket (Q i) cZ.c (cZ.G j)
      obtain ⟨b1, b2⟩ := ConZonotope.aux_quadBil_bracket (Q i) (cZ.G j) cZ.c
      have h1 := addDown_le_add (ConZonotope.quadBilDown (Q i) cZ.c (cZ.G j))
        (ConZonotope.quadBilDown (Q i) (cZ.G j) cZ.c)
      have h2 := add_le_addUp (ConZonotope.quadBilUp (Q i) cZ.c (cZ.G j))
        (ConZonotope.quadBilUp (Q i) (cZ.G j) cZ.c)
      simp only [ConZonotope.quadMapGDown, ConZonotope.quadMapGUp, ConZonotope.aux_quadMapGReal,
        Fin.append_left]
      exact ⟨by linarith, by linarith⟩
    · -- the square, half of one bilinear form
      obtain ⟨a1, a2⟩ := ConZonotope.aux_quadBil_bracket (Q i) (cZ.G j)
        (cZ.G j)
      simp only [ConZonotope.quadMapGDown, ConZonotope.quadMapGUp, ConZonotope.aux_quadMapGReal,
        Fin.append_left, Fin.append_right, toReal_half]
      exact ⟨by linarith, by linarith⟩
  · -- the pairs, a sum off the diagonal and zero on it
    by_cases hjk : (finProdFinEquiv.symm l).1 < (finProdFinEquiv.symm l).2
    · obtain ⟨a1, a2⟩ := ConZonotope.aux_quadBil_bracket (Q i)
        (cZ.G (finProdFinEquiv.symm l).1) (cZ.G (finProdFinEquiv.symm l).2)
      -- both orders of the pair, each bracketed
      obtain ⟨b1, b2⟩ := ConZonotope.aux_quadBil_bracket (Q i)
        (cZ.G (finProdFinEquiv.symm l).2) (cZ.G (finProdFinEquiv.symm l).1)
      have h1 := addDown_le_add
        (ConZonotope.quadBilDown (Q i) (cZ.G (finProdFinEquiv.symm l).1)
          (cZ.G (finProdFinEquiv.symm l).2))
        (ConZonotope.quadBilDown (Q i) (cZ.G (finProdFinEquiv.symm l).2)
          (cZ.G (finProdFinEquiv.symm l).1))
      have h2 := add_le_addUp
        (ConZonotope.quadBilUp (Q i) (cZ.G (finProdFinEquiv.symm l).1)
          (cZ.G (finProdFinEquiv.symm l).2))
        (ConZonotope.quadBilUp (Q i) (cZ.G (finProdFinEquiv.symm l).2)
          (cZ.G (finProdFinEquiv.symm l).1))
      simp only [ConZonotope.quadMapGDown, ConZonotope.quadMapGUp, ConZonotope.aux_quadMapGReal,
        Fin.append_right, if_pos hjk]
      exact ⟨by linarith, by linarith⟩
    · simp only [ConZonotope.quadMapGDown, ConZonotope.quadMapGUp, ConZonotope.aux_quadMapGReal,
        Fin.append_right, if_neg hjk, toReal_zero]
      exact ⟨le_refl _, le_refl _⟩


/-- A stored generator of `quadMap` is within its gap of the exact one. -/
private theorem ConZonotope.aux_quadMapG_close (Q : Fin m → Mat 𝕋 n n)
    (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (i : Fin m)
    (l : Fin (cZ.h + cZ.h + cZ.h * cZ.h)) : -- --- CONCL ---
    |(Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ)).G l i
        - toReal (ConZonotope.quadMapGDown Q cZ i l)|
      ≤ toReal (ConZonotope.quadMapGDiff Q cZ i l) := by -- --- PROOF ---
  -- the exact layer's generator is the table at this layer's index type
  have hreal : (Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ)).G l i
      = ConZonotope.aux_quadMapGReal Q cZ i l := rfl
  rw [hreal]
  obtain ⟨h1, h2⟩ := ConZonotope.aux_quadMapG_between Q cZ i l
  have h3 := sub_le_subUp (ConZonotope.quadMapGUp Q cZ i l) (ConZonotope.quadMapGDown Q cZ i l)
  rw [abs_le]
  simp only [ConZonotope.quadMapGDiff]
  constructor <;> linarith


/-- The exact center of `quadMap` lies between the two stored roundings. -/
private theorem ConZonotope.aux_quadMapC_between (Q : Fin m → Mat 𝕋 n n)
    (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (i : Fin m) : -- --- CONCL ---
    toReal (ConZonotope.quadMapCDown Q cZ i)
        ≤ (Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ)).c i
      ∧ (Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ)).c i
        ≤ toReal (ConZonotope.quadMapCUp Q cZ i) := by -- --- PROOF ---
  -- the exact center, with the generators read back as `toRealVec` reads them
  have hR : (Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ)).c i
      = toRealVec cZ.c ⬝ᵥ (toRealMat (Q i) *ᵥ toRealVec cZ.c)
        + 1 / 2 * ∑ s, (toRealVec (cZ.G s)) ⬝ᵥ
          (toRealMat (Q i) *ᵥ toRealVec (cZ.G s)) := rfl
  rw [hR]
  obtain ⟨a1, a2⟩ := ConZonotope.aux_quadBil_bracket (Q i) cZ.c cZ.c
  -- the sum of the generators' forms, from either side
  have hs1 := sumDown_le_sum fun s =>
    ConZonotope.quadBilDown (Q i) (cZ.G s) (cZ.G s)
  have hs2 := sum_le_sumUp fun s =>
    ConZonotope.quadBilUp (Q i) (cZ.G s) (cZ.G s)
  have hlo : ∑ s, toReal (ConZonotope.quadBilDown (Q i) (cZ.G s) (cZ.G s))
      ≤ ∑ s, (toRealVec (cZ.G s)) ⬝ᵥ
          (toRealMat (Q i) *ᵥ toRealVec (cZ.G s)) :=
    Finset.sum_le_sum fun s _ => (ConZonotope.aux_quadBil_bracket (Q i) _ _).1
  have hhi : ∑ s, (toRealVec (cZ.G s)) ⬝ᵥ
          (toRealMat (Q i) *ᵥ toRealVec (cZ.G s))
      ≤ ∑ s, toReal (ConZonotope.quadBilUp (Q i) (cZ.G s) (cZ.G s)) :=
    Finset.sum_le_sum fun s _ => (ConZonotope.aux_quadBil_bracket (Q i) _ _).2
  have hd := addDown_le_add (ConZonotope.quadBilDown (Q i) cZ.c cZ.c)
    (half (sumDown fun s =>
      ConZonotope.quadBilDown (Q i) (cZ.G s) (cZ.G s)))
  have hu := add_le_addUp (ConZonotope.quadBilUp (Q i) cZ.c cZ.c)
    (half (sumUp fun s => ConZonotope.quadBilUp (Q i) (cZ.G s) (cZ.G s)))
  simp only [ConZonotope.quadMapCDown, ConZonotope.quadMapCUp, toReal_half] at hd hu ⊢
  constructor <;> linarith


/-- The quadratic image of the nominal set, on the factors of `quadMapDep`. -/
private theorem ConZonotope.aux_quadMapDep_nominal (Q : Fin m → Mat 𝕋 n n)
    (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
    (fun x : Vec ℝ n => fun i => x ⬝ᵥ (toRealMat (Q i) *ᵥ x)) '' nominalSet cZ
      ⊆ nominalSet (ConZonotope.quadMapDep Q cZ)
        + (I_error (ConZonotope.quadMapDep Q cZ)).construct := by -- --- PROOF ---
  rintro _ ⟨z, hz, rfl⟩
  -- the exact layer's quadratic map of the read-back operand, named once
  set R := Real.ConZonotope.quadMap (fun k => toRealMat (Q k)) (nominal cZ) with hR
  -- the exact layer's enclosure, on the read-back operand
  obtain ⟨β, hβ, hP, hx⟩ := Real.ConZonotope.quadMap_outer (fun k => toRealMat (Q k))
    (nominal cZ) ⟨z, hz, rfl⟩
  -- the same coefficients, spelt at this layer's index type
  obtain ⟨β', hβ', hP', hx'⟩ : ∃ β' : Fin (cZ.h + cZ.h + cZ.h * cZ.h) → ℝ, (∀ j, |β' j| ≤ 1)
      ∧ β' ∈ (ConZonotope.quadMapDep Q cZ).P.nominal.construct
      ∧ ∀ i, (fun x : Vec ℝ n => fun i => x ⬝ᵥ (toRealMat (Q i) *ᵥ x)) z i
        = R.c i
          + ∑ l, β' l
            * R.G l i := by
    refine ⟨β, hβ, ?_, fun i => ?_⟩
    -- the constraints of the exact form are the operand's, pulled back through two blocks
    · exact HPolytope.mem_padLeft_nominal_iff.mpr (HPolytope.mem_padLeft_nominal_iff.mpr hP)
    · have := congrFun hx i
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      exact this
  -- the two shortfalls, in the box the stored zonotope carries
  have hd₁ : (fun i => R.c i
        - toReal (ConZonotope.quadMapCDown Q cZ i))
      ∈ (Interval.residual (ConZonotope.quadMapCDown Q cZ) (ConZonotope.quadMapCUp Q cZ)
        (ConZonotope.quadMapCDown Q cZ)).construct :=
    Interval.sub_mem_residual fun i => ConZonotope.aux_quadMapC_between Q cZ i
  have hd₂ : (fun i => ∑ l, (R.G l i - toReal (ConZonotope.quadMapGDown Q cZ i l)) * β' l)
      ∈ (Zonotope.generatorError (ConZonotope.quadMapGDiff Q cZ)).construct :=
    Zonotope.mem_generatorError (fun i l => ConZonotope.aux_quadMapG_close Q cZ i l) hβ'
  -- the stored nominal point at `β'`
  refine ⟨_, ConZonotope.mem_nominalSet_iff.mpr ⟨β', hβ', hP', fun _ => rfl⟩, _,
    Interval.plus_outer _ _ ⟨_, hd₁, _, hd₂, rfl⟩, ?_⟩
  funext i
  -- the stored point and the two shortfalls, coordinate `i`
  show toReal (ConZonotope.quadMapCDown Q cZ i)
      + ∑ l, toReal (ConZonotope.quadMapGDown Q cZ i l) * β' l
      + (R.c i
          - toReal (ConZonotope.quadMapCDown Q cZ i)
        + ∑ l, (R.G l i
          - toReal (ConZonotope.quadMapGDown Q cZ i l)) * β' l)
      = z ⬝ᵥ (toRealMat (Q i) *ᵥ z)
  have hsplit : ∑ l, (R.G l i
        - toReal (ConZonotope.quadMapGDown Q cZ i l)) * β' l
      = ∑ l, β' l * R.G l i
        - ∑ l, toReal (ConZonotope.quadMapGDown Q cZ i l) * β' l := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hsplit]
  have e := hx' i
  simp only at e
  linarith [e]

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.quadMap_outer (Q : Fin m → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) :
    (fun x : Vec ℝ n => fun i => x ⬝ᵥ (toRealMat (Q i) *ᵥ x)) '' cZ.construct
      ⊆ (cZ.quadMap Q).construct := by
  rintro _ ⟨x, hx, rfl⟩
  exact ConZonotope.aux_quadMapDep_nominal Q cZ.absorbRounding
    ⟨x, ConZonotope.absorbRounding_nominal cZ hx, rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
