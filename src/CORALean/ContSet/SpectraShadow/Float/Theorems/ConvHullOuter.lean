import CORALean.ContSet.SpectraShadow.Float.Operations.ConvHull
import CORALean.ContSet.SpectraShadow.Float.Theorems.ConeOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.CartProdOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.PlusOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.InterOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.ProjectOuter
import CORALean.ContSet.SpectraShadow.Float.Theorems.Convex
import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
import Mathlib.Analysis.Convex.Hull

/-!
# `SpectraShadow.convHull_` encloses the convex hull of the union, over a floating-point scalar

Each of the two shadows is inside the result: a point `x` of `S₁` is `1 · (x, 1)`, a point of the
cone of `S₁ × {1}`, plus the origin of the other cone, at height `1`, and the projection gives `x`
back. The result is convex, so it holds the hull. Outer: the cones are exact but their sum
rounds the centre into the box.
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

theorem SpectraShadow.aux_singletonOne_mem :
    (fun _ : Fin 1 => (1 : ℝ))
      ∈ (SpectraShadow.singletonOne : SpectraShadow 𝕋 (Vec 𝕋 1)).construct := by -- --- PROOF ---
  -- the error box is the origin, and the nominal part holds `1` at `β = 1`
  have hE : (0 : Vec ℝ 1) ∈
    (SpectraShadow.singletonOne : SpectraShadow 𝕋 (Vec 𝕋 1)).E.construct := by
    rw [show (SpectraShadow.singletonOne : SpectraShadow 𝕋 (Vec 𝕋 1)).E =
      Interval.origin 1 from rfl,
      Interval.origin_exact]; rfl
  refine ⟨_, ?_, 0, hE, add_zero _⟩
  -- the nominal part, witnessed by `β = 1`
  refine SpectraShadow.mem_nominalSet_iff.2 ⟨fun _ => 1, ?_, fun i => ?_⟩
  · have : toRealMat (SpectraShadow.singletonOne : SpectraShadow 𝕋 (Vec 𝕋 1)).A₀
        + ∑ i, (fun _ : Fin 1 => (1 : ℝ)) i •
          toRealMat ((SpectraShadow.singletonOne : SpectraShadow 𝕋 (Vec 𝕋 1)).A i) =
            (0 : Mat ℝ 2 2) := by
      ext p q
      fin_cases p <;> fin_cases q <;>
        simp [toRealMat, SpectraShadow.singletonOne, toReal_one, toReal_zero, toReal_neg]
    show Matrix.PosSemidef (toRealMat (SpectraShadow.singletonOne : SpectraShadow 𝕋 (Vec 𝕋 1)).A₀
        + ∑ i, (fun _ : Fin 1 => (1 : ℝ)) i •
          toRealMat ((SpectraShadow.singletonOne : SpectraShadow 𝕋 (Vec 𝕋 1)).A i))
    rw [this]
    exact Matrix.PosSemidef.zero
  · simp [SpectraShadow.singletonOne, toReal_zero, toReal_one]

theorem SpectraShadow.aux_hyperplaneOne_mem (y : Vec ℝ n) :
    (Fin.append y (fun _ : Fin 1 => (1 : ℝ)) : Vec ℝ (n + 1))
      ∈ (SpectraShadow.hyperplaneOne 𝕋 n).construct := by -- --- PROOF ---
  have hE : (0 : Vec ℝ (n + 1)) ∈ (SpectraShadow.hyperplaneOne 𝕋 n).E.construct := by
    rw [show (SpectraShadow.hyperplaneOne 𝕋 n).E = Interval.origin (n + 1) from rfl,
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

theorem SpectraShadow.convHull_outer (S₁ S₂ : SpectraShadow 𝕋 (Vec 𝕋 n)) :
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
    SpectraShadow.cone_outer (Nat.succ_pos n) _
      (Or.inr ⟨1, one_pos, _, happ S x hx, (one_smul _ _).symm⟩)
  -- the origin is in every cone
  have h0 : ∀ (S : SpectraShadow 𝕋 (Vec 𝕋 n)), (0 : Vec ℝ (n + 1))
      ∈ (S.cartProd SpectraShadow.singletonOne).cone.construct := fun S =>
    SpectraShadow.cone_outer (Nat.succ_pos n) _ (Or.inl rfl)
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
