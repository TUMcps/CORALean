module

public import CORALean.ContSet.SpectraShadow.Float.Operations.CartProd
public import CORALean.ContSet.InflatedContSet.Theorems.ImageSubset
public import CORALean.ContSet.SpectraShadow.Float.Operations.PadLeft
public import CORALean.ContSet.SpectraShadow.Real.Theorems.MapExact
public import CORALean.ContSet.SpectraShadow.Float.Operations.PadRight
public import CORALean.ContSet.SpectraShadow.Float.Theorems.PlusOuter
public import CORALean.Global.Block

@[expose] public section

/-!
# `SpectraShadow.cartProd` contains the Cartesian product

The product's points are the sums of the two embeddings, each inside its padded shadow, and
`plus_outer` takes the sum of the padded shadows into the result.

## Inputs
* `S` – spectrahedral shadow
* `T` – spectrahedral shadow

## Hypotheses
* none

## Conclusion
* `SpectraShadow.cartProd` contains the Cartesian product
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
open FloatOps InflatedContSet

/-- The padded stored shadow reads as the nominal shadow mapped by the embedding. -/
theorem SpectraShadow.aux_padRight_nominal (S : SpectraShadow 𝕋 (Vec 𝕋 m)) : -- --- CONCL ---
    nominal (S.padRight n) = (nominal S).map (blockPadRight n m) := by -- --- PROOF ---
  show Real.SpectraShadow.mk _ _ _ _ _ _ = Real.SpectraShadow.mk _ _ _ _ _ _
  congr 1
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [realImage_vec]
      simp [SpectraShadow.padRight, blockPadRight, toRealVec, toReal_zero]
    · rw [realImage_vec]
      simp [SpectraShadow.padRight, blockPadRight, toRealVec]
      rfl
  · funext j
    funext i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · rw [realImage_vec]
      simp [SpectraShadow.padRight, blockPadRight, toRealVec, toReal_zero]
    · rw [realImage_vec]
      simp [SpectraShadow.padRight, blockPadRight, toRealVec]
      rfl


/-- `SpectraShadow.padRight` contains the embedded shadow. -/
theorem SpectraShadow.aux_padRight_outer (n : ℕ) (S : SpectraShadow 𝕋 (Vec 𝕋 m)) :
    ⇑(blockPadRight n m) '' S.construct ⊆ (S.padRight n).construct :=
  image_subset (fun _ _ => map_add _ _ _)
    (by
      show ⇑(blockPadRight n m) '' nominalSet S ⊆ ContSet.construct (nominal (S.padRight n))
      rw [SpectraShadow.aux_padRight_nominal]
      exact le_of_eq (Real.SpectraShadow.map_exact _ _))
    (by
      rintro _ ⟨e, he, rfl⟩ i
      show toReal ((Fin.append (fun _ : Fin n => zero) S.I_error.inf) i) ≤ (Fin.append 0 e) i
        ∧ (Fin.append 0 e) i ≤ toReal ((Fin.append (fun _ : Fin n => zero) S.I_error.sup) i)
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [toReal_zero]
      · have h : toReal (S.I_error.inf j) ≤ e j ∧ e j ≤ toReal (S.I_error.sup j) := he j
        simpa using h)

end


section
open FloatOps InflatedContSet

/-- The padded stored shadow reads as the nominal shadow mapped by the embedding. -/
theorem SpectraShadow.aux_padLeft_nominal (S : SpectraShadow 𝕋 (Vec 𝕋 n)) : -- --- CONCL ---
    nominal (S.padLeft m) = (nominal S).map (blockPadLeft n m) := by -- --- PROOF ---
  show Real.SpectraShadow.mk _ _ _ _ _ _ = Real.SpectraShadow.mk _ _ _ _ _ _
  congr 1
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [realImage_vec]
      simp [SpectraShadow.padLeft, blockPadLeft, toRealVec]
      rfl
    · rw [realImage_vec]
      simp [SpectraShadow.padLeft, blockPadLeft, toRealVec, toReal_zero]
  · funext j
    funext i
    refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · rw [realImage_vec]
      simp [SpectraShadow.padLeft, blockPadLeft, toRealVec]
      rfl
    · rw [realImage_vec]
      simp [SpectraShadow.padLeft, blockPadLeft, toRealVec, toReal_zero]


/-- `SpectraShadow.padLeft` contains the embedded shadow. -/
theorem SpectraShadow.aux_padLeft_outer (S : SpectraShadow 𝕋 (Vec 𝕋 n)) (m : ℕ) :
    ⇑(blockPadLeft n m) '' S.construct ⊆ (S.padLeft m).construct :=
  image_subset (fun _ _ => map_add _ _ _)
    (by
      show ⇑(blockPadLeft n m) '' nominalSet S ⊆ ContSet.construct (nominal (S.padLeft m))
      rw [SpectraShadow.aux_padLeft_nominal]
      exact le_of_eq (Real.SpectraShadow.map_exact _ _))
    (by
      rintro _ ⟨e, he, rfl⟩ i
      show toReal ((Fin.append S.I_error.inf fun _ => zero) i) ≤ (Fin.append e 0) i
        ∧ (Fin.append e 0) i ≤ toReal ((Fin.append S.I_error.sup fun _ => zero) i)
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · have h : toReal (S.I_error.inf j) ≤ e j ∧ e j ≤ toReal (S.I_error.sup j) := he j
        simpa using h
      · simp [toReal_zero])

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.cartProd_outer (S : SpectraShadow 𝕋 (Vec 𝕋 n))
    (T : SpectraShadow 𝕋 (Vec 𝕋 m)) : -- --- CONCL ---
    (fun p : Vec ℝ n × Vec ℝ m => (Fin.append p.1 p.2 : Vec ℝ (n + m)))
      '' (S.construct ×ˢ T.construct) ⊆ (S.cartProd T).construct := by -- --- PROOF ---
  rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
  refine SpectraShadow.plus_outer _ _ ?_
  -- the point is the sum of its two embeddings, one in each padded shadow
  have hsum : blockPadLeft n m x + blockPadRight n m y = Fin.append x y := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [blockPadLeft, blockPadRight]
  exact ⟨_, SpectraShadow.aux_padLeft_outer S m ⟨x, hx, rfl⟩, _,
    SpectraShadow.aux_padRight_outer n T ⟨y, hy, rfl⟩, hsum⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
