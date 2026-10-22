module

public import CORALean.ContSet.SpectraShadow.Float.Operations.ConvHull
public import CORALean.ContSet.SpectraShadow.Float.Theorems.CartProdOuter
public import CORALean.ContSet.SpectraShadow.Float.Operations.Cone
public import CORALean.ContSet.SpectraShadow.Float.Theorems.AbsorbRoundingNominal
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatBlockDiag
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatConstZero
public import CORALean.ContSet.SpectraShadow.Real.Theorems.ConeConstruct
public import CORALean.ContSet.Interval.Float.Theorems.OriginExact
public import CORALean.ContSet.SpectraShadow.Float.Theorems.Convex
public import CORALean.ContSet.SpectraShadow.Float.Theorems.InterOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MaterialiseEq
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
public import CORALean.ContSet.SpectraShadow.Float.Theorems.PlusOuter
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ProjectOuter
public import Mathlib.Analysis.Convex.Hull

@[expose] public section

/-!
# `SpectraShadow.convHull_` encloses the convex hull of the union, over a floating-point scalar

Each of the two shadows is inside the result: a point `x` of `S₁` is `1 · (x, 1)`, a point of the
cone of `S₁ × {1}`, plus the origin of the other cone, at height `1`, and the projection gives `x`
back. The result is convex, so it holds the hull. Outer: the cones are exact but their sum
rounds the center into the box.

## Inputs
* `S₁` – spectrahedral shadow
* `S₂` – spectrahedral shadow

## Hypotheses
* none

## Conclusion
* `SpectraShadow.convHull_` encloses the convex hull of the union, over a floating-point scalar
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic CORALean

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N : ℕ}

theorem aux_toRealMat_arrowMat (s t : 𝕋) (w : Vec 𝕋 N) : -- --- CONCL ---
    toRealMat (arrowMat s t w)
      = Real.arrowMat (toReal s) (toReal t) (toRealVec w) := by -- --- PROOF ---
  -- each of the four cases of an entry
  ext p q
  refine Fin.cases ?_ (fun i => ?_) p <;> refine Fin.cases ?_ (fun j => ?_) q <;>
    simp [toRealMat, arrowMat, Real.arrowMat, toRealVec]
  split_ifs <;> simp [toReal_zero]


theorem SpectraShadow.aux_nominal_cone (T : SpectraShadow 𝕋 (Vec 𝕋 N)) : -- --- CONCL ---
    InflatedContSet.nominal T.cone
      = Real.SpectraShadow.cone (InflatedContSet.nominal T.absorbRounding) := by -- --- PROOF ---
  -- the six fields: the sizes agree, the matrices, center and generators entry by entry
  unfold SpectraShadow.cone Real.SpectraShadow.cone
  show Real.SpectraShadow.mk _ _ _ _ _ _ = Real.SpectraShadow.mk _ _ _ _ _ _
  congr 1
  · exact SpectraShadow.toRealMat_const_zero
  -- the family of matrices, by the layer of the index
  · funext i
    induction i using Fin.addCases with
    | left p =>
      induction p using Fin.addCases with
      -- the layer of `s`
      | left a =>
        simp only [Fin.append_left]
        simp [SpectraShadow.toRealMat_blockDiag, aux_toRealMat_arrowMat, toReal_one, toReal_zero,
          InflatedContSet.nominal, RealImage.realImage]
      | right j =>
        simp only [Fin.append_left, Fin.append_right]
        simp [SpectraShadow.toRealMat_blockDiag, aux_toRealMat_arrowMat, toReal_zero,
          InflatedContSet.nominal]
        rfl
    -- the layer of the auxiliary variable `t`
    | right q =>
      simp only [Fin.append_right]
      erw [Fin.append_right]
      have h0 : toRealVec (fun _ : Fin N => (zero : 𝕋)) = 0 := by
        funext i; simp [toRealVec, toReal_zero]
      simp [SpectraShadow.toRealMat_blockDiag, aux_toRealMat_arrowMat, toReal_zero, toReal_one,
        SpectraShadow.toRealMat_const_zero, h0]
  · funext i
    simp [RealImage.realImage, toRealVec, toReal_zero]
  -- the generators
  · funext j i
    induction j using Fin.addCases with
    | left p =>
      induction p using Fin.addCases with
      | left a => simp [InflatedContSet.nominal]
      | right k => simp [InflatedContSet.nominal]
    | right q =>
      erw [Fin.append_right]
      simp [RealImage.realImage, toRealVec, toReal_zero]


/-- The float cone encloses the perspective cone. -/
theorem SpectraShadow.aux_cone_outer (hN : 0 < N) (T : SpectraShadow 𝕋 (Vec 𝕋 N)) : -- --- CONCL ---
    {z : Vec ℝ N | z = 0 ∨ ∃ s : ℝ, 0 < s ∧ ∃ x ∈ T.construct, z = s • x}
      ⊆ T.cone.construct := by -- --- PROOF ---
  -- the point is in the nominal part, by the exact layer's description of the cone
  intro z hz
  have hnom : z ∈ InflatedContSet.nominalSet T.cone := by
    change z ∈ ContSet.construct (InflatedContSet.nominal T.cone)
    rw [SpectraShadow.aux_nominal_cone]
    change z ∈ (Real.SpectraShadow.cone (InflatedContSet.nominal T.absorbRounding)).construct
    rw [Real.SpectraShadow.cone_construct hN]
    rcases hz with rfl | ⟨s, hs, x, hx, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨s, hs, x, T.absorbRounding_nominal hx, rfl⟩
  have hE : T.cone.I_error.construct = {0} := Interval.origin_exact N
  refine ⟨z, hnom, 0, ?_, add_zero z⟩
  rw [show T.cone.I_error = Interval.origin N from rfl] at hE
  exact (by
    rw [InflatedContSet.I_error]
    exact hE ▸ rfl : (0 : Vec ℝ N) ∈ (InflatedContSet.I_error T.cone).construct)

end


theorem SpectraShadow.aux_singletonOne_mem : -- --- CONCL ---
    (fun _ : Fin 1 => (1 : ℝ))
      ∈ (SpectraShadow.singletonOne : SpectraShadow 𝕋 (Vec 𝕋 1)).construct := by -- --- PROOF ---
  -- the one-dimensional set `{1}`, named once
  set S1 : SpectraShadow 𝕋 (Vec 𝕋 1) := SpectraShadow.singletonOne
  -- the error box is the origin, and the nominal part holds `1` at `β = 1`
  have hE : (0 : Vec ℝ 1) ∈ S1.I_error.construct := by
    rw [show S1.I_error = Interval.origin 1 from rfl, Interval.origin_exact]; rfl
  refine ⟨_, ?_, 0, hE, add_zero _⟩
  -- the nominal part, witnessed by `β = 1`
  refine SpectraShadow.mem_nominalSet_iff.2 ⟨fun _ => 1, ?_, fun i => ?_⟩
  · have : toRealMat S1.A₀ + ∑ i, (fun _ : Fin 1 => (1 : ℝ)) i • toRealMat (S1.A i)
        = (0 : Mat ℝ 2 2) := by
      ext p q
      fin_cases p <;> fin_cases q <;>
        simp [toRealMat, S1, SpectraShadow.singletonOne, toReal_one, toReal_zero, toReal_neg]
    show Matrix.PosSemidef
      (toRealMat S1.A₀ + ∑ i, (fun _ : Fin 1 => (1 : ℝ)) i • toRealMat (S1.A i))
    rw [this]
    exact Matrix.PosSemidef.zero
  · simp [S1, SpectraShadow.singletonOne, toReal_zero, toReal_one]

theorem SpectraShadow.aux_hyperplaneOne_mem (y : Vec ℝ n) : -- --- CONCL ---
    (Fin.append y (fun _ : Fin 1 => (1 : ℝ)) : Vec ℝ (n + 1))
      ∈ (SpectraShadow.hyperplaneOne 𝕋 n).construct := by -- --- PROOF ---
  have hE : (0 : Vec ℝ (n + 1)) ∈ (SpectraShadow.hyperplaneOne 𝕋 n).I_error.construct := by
    rw [show (SpectraShadow.hyperplaneOne 𝕋 n).I_error = Interval.origin (n + 1) from rfl,
      Interval.origin_exact]; rfl
  refine ⟨_, ?_, 0, hE, add_zero _⟩
  refine SpectraShadow.mem_nominalSet_iff.2 ⟨y, ?_, fun i => ?_⟩
  · have hA0 : toRealMat (SpectraShadow.hyperplaneOne 𝕋 n).A₀ = (0 : Mat ℝ 1 1) :=
      SpectraShadow.toRealMat_const_zero
    show Matrix.PosSemidef (toRealMat (SpectraShadow.hyperplaneOne 𝕋 n).A₀
      + ∑ i, y i • toRealMat ((SpectraShadow.hyperplaneOne 𝕋 n).A i))
    simp only [hA0, smul_zero, Finset.sum_const_zero, add_zero]
    exact Matrix.PosSemidef.zero
  · induction i using Fin.addCases with
    | left p =>
      simp [SpectraShadow.hyperplaneOne, toReal_zero, toReal_one, apply_ite toReal]
    | right q =>
      obtain rfl : q = 0 := Subsingleton.elim _ _
      simp [SpectraShadow.hyperplaneOne, toReal_zero, toReal_one]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.convHull_outer (S₁ S₂ : SpectraShadow 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
    convexHull ℝ (S₁.construct ∪ S₂.construct) ⊆ (S₁.convHull_ S₂).construct := by -- --- PROOF ---
  unfold SpectraShadow.convHull_
  simp only [SpectraShadow.materialise_eq]
  refine convexHull_min ?_ (SpectraShadow.convex_construct _)
  -- a point `x` of a shadow, at height one, is in the product with `{1}`
  have happ : ∀ (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (x : Vec ℝ n), x ∈ S.construct →
      (Fin.append x (fun _ : Fin 1 => (1 : ℝ)) : Vec ℝ (n + 1))
        ∈ (S.cartProd SpectraShadow.singletonOne).construct := fun S x hx =>
    SpectraShadow.cartProd_outer S SpectraShadow.singletonOne
      ⟨(x, fun _ => 1), ⟨hx, SpectraShadow.aux_singletonOne_mem⟩, rfl⟩
  -- and in the cone of the product (`s = 1`)
  have hcone : ∀ (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (x : Vec ℝ n), x ∈ S.construct →
      (Fin.append x (fun _ : Fin 1 => (1 : ℝ)) : Vec ℝ (n + 1))
        ∈ (S.cartProd SpectraShadow.singletonOne).cone.construct := fun S x hx =>
    SpectraShadow.aux_cone_outer (Nat.succ_pos n) _
      (Or.inr ⟨1, one_pos, _, happ S x hx, (one_smul _ _).symm⟩)
  -- the origin is in every cone
  have h0 : ∀ (S : SpectraShadow 𝕋 (Vec 𝕋 n)), (0 : Vec ℝ (n + 1))
      ∈ (S.cartProd SpectraShadow.singletonOne).cone.construct := fun S =>
    SpectraShadow.aux_cone_outer (Nat.succ_pos n) _ (Or.inl rfl)
  -- a point at height one of a sum of cones is in the hyperplane and projects to `x`
  have hfin : ∀ (A : SpectraShadow 𝕋 (Vec 𝕋 (n + 1))) (x : Vec ℝ n),
      (Fin.append x (fun _ : Fin 1 => (1 : ℝ)) : Vec ℝ (n + 1)) ∈ A.construct →
      x ∈ ((A.inter (SpectraShadow.hyperplaneOne 𝕋 n)).project (Fin.castAdd 1)).construct :=
    fun A x hA =>
    SpectraShadow.project_outer _ _
      ⟨_, SpectraShadow.inter_outer _ _ ⟨hA, SpectraShadow.aux_hyperplaneOne_mem x⟩,
        funext fun k => by simp⟩
  -- a point of either shadow is `(x, 1)` plus the origin of the other cone
  rintro x (hx | hx)
  · exact hfin _ x (SpectraShadow.plus_outer _ _ ⟨_, hcone S₁ x hx, 0, h0 S₂, add_zero _⟩)
  · exact hfin _ x (SpectraShadow.plus_outer _ _ ⟨0, h0 S₁, _, hcone S₂ x hx, zero_add _⟩)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
