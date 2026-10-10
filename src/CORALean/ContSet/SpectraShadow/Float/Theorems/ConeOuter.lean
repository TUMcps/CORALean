import CORALean.ContSet.SpectraShadow.Float.Operations.Cone
import CORALean.ContSet.SpectraShadow.Float.Theorems.ConstructSubsetAbsorb
import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatBlockDiag
import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatConstZero
import CORALean.ContSet.SpectraShadow.Real.Theorems.ConeConstruct
import CORALean.ContSet.Interval.Float.Theorems.OriginExact

/-!
# The float cone encloses the perspective cone

The nominal part of `Float.SpectraShadow.cone T` is the exact layer's `cone` of the nominal part
of `T.absorb`: every stored entry is a stored float, `zero` or `one`, and reads as it. So
`Real.SpectraShadow.cone_construct` describes it, and the box is the origin. Every point `s x` of
`T`'s set, `s > 0`, and the origin are in it: outer, as the set of `T` is inside the absorbed
nominal shadow.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic CORALean

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem aux_toRealMat_arrowMat (s t : 𝕋) (w : Vec 𝕋 N) :
    toRealMat (arrowMat s t w)
      = Real.arrowMat (toReal s) (toReal t) (toRealVec w) := by -- --- PROOF ---
  -- each of the four cases of an entry
  ext p q
  refine Fin.cases ?_ (fun i => ?_) p <;> refine Fin.cases ?_ (fun j => ?_) q <;>
    simp [toRealMat, arrowMat, Real.arrowMat, toRealVec]
  split_ifs <;> simp [toReal_zero]

theorem SpectraShadow.aux_nominal_cone (T : SpectraShadow 𝕋 N) :
    InflatedContSet.nominal T.cone
      = Real.SpectraShadow.cone (InflatedContSet.nominal T.absorb) := by -- --- PROOF ---
  -- the six fields: the sizes agree, the matrices, centre and generators entry by entry
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.cone_outer (hN : 0 < N) (T : SpectraShadow 𝕋 N) :
    {z : Vec ℝ N | z = 0 ∨ ∃ s : ℝ, 0 < s ∧ ∃ x ∈ T.construct, z = s • x}
      ⊆ T.cone.construct := by -- --- PROOF ---
  -- the point is in the nominal part, by the exact layer's description of the cone
  intro z hz
  have hnom : z ∈ InflatedContSet.nominalSet T.cone := by
    change z ∈ ContSet.construct (InflatedContSet.nominal T.cone)
    rw [SpectraShadow.aux_nominal_cone]
    change z ∈ (Real.SpectraShadow.cone (InflatedContSet.nominal T.absorb)).construct
    rw [Real.SpectraShadow.cone_construct hN]
    rcases hz with rfl | ⟨s, hs, x, hx, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨s, hs, x, T.construct_subset_absorb hx, rfl⟩
  have hE : T.cone.E.construct = {0} := Interval.origin_exact N
  refine ⟨z, hnom, 0, ?_, add_zero z⟩
  rw [show T.cone.E = Interval.origin N from rfl] at hE
  exact (by
    rw [InflatedContSet.error]
    exact hE ▸ rfl : (0 : Vec ℝ N) ∈ (InflatedContSet.error T.cone).construct)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
