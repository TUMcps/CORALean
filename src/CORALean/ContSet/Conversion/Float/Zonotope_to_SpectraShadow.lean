module

public import CORALean.ContSet.Conversion.Real.Zonotope_to_SpectraShadow
public import CORALean.ContSet.InflatedContSet.Theorems.MonoSubset
public import CORALean.ContSet.SpectraShadow.Float.Theorems.ToRealMatBlockDiag
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_SpectraShadow

@[expose] public section

/-!
# A zonotope as a spectrahedral shadow, over a floating-point scalar

The exact layer's diagonal inequality with `one`, `neg one` and `zero` as its
entries, all stored exactly, and the zonotope's own centre, generators and error
box: nothing rounds, so nothing is paid.

Not routed through the exact layer's set — the stored matrices read as reals only
up to `toReal_one`, `toReal_neg` and `toReal_zero` — but through its *nominal*
reading, which is the exact conversion of the zonotope the stored floats describe,
and that shares the exactness proof.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Zonotope.aux_toRealMat_unitDiag {h : ℕ} (s : 𝕋) (j : Fin h) :
    toRealMat (Zonotope.unitDiag s j) = Matrix.diagonal (Pi.single j (toReal s)) := by
  ext p q
  simp only [toRealMat, Zonotope.unitDiag, Matrix.diagonal_apply, Pi.single_apply]
  split_ifs <;> simp [toReal_zero]

theorem Zonotope.aux_toRealMat_one {h : ℕ} :
    toRealMat (fun (i j : Fin h) => if i = j then (one : 𝕋) else zero) = 1 := by
  ext p q
  simp only [toRealMat, Matrix.one_apply]
  split_ifs <;> simp [toReal_zero, toReal_one]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The stored inequality at a point of the cube is positive semidefinite: the exact layer's, read
through the stored entries. -/
theorem Zonotope.posSemidef_spectraShadow (Z : Zonotope (Vec 𝕋 n)) (β : Fin Z.h → ℝ)
    (hβ : ∀ j, |β j| ≤ 1) :
    (toRealMat Z.spectraShadow.A₀
        + ∑ j : Fin Z.h, β j • toRealMat (Z.spectraShadow.A j)).PosSemidef := by -- --- PROOF ---
  have hP := (Real.Zonotope.posSemidef_spectraShadow_iff (nominal Z) β).mpr hβ
  -- the stored matrices read as the exact layer's
  have h₀ : toRealMat Z.spectraShadow.A₀ = (nominal Z).spectraShadow.A₀ := by
    have h := SpectraShadow.toRealMat_blockDiag (𝕋 := 𝕋)
      (fun i j : Fin Z.h => if i = j then (one : 𝕋) else zero)
      (fun i j : Fin Z.h => if i = j then (one : 𝕋) else zero)
    rw [Zonotope.aux_toRealMat_one] at h
    exact h
  have hA : ∀ j, toRealMat (Z.spectraShadow.A j) = (nominal Z).spectraShadow.A j := fun j => by
    have h := SpectraShadow.toRealMat_blockDiag (𝕋 := 𝕋) (Zonotope.unitDiag one j)
      (Zonotope.unitDiag (neg one) j)
    rw [Zonotope.aux_toRealMat_unitDiag, Zonotope.aux_toRealMat_unitDiag, toReal_one,
      toReal_neg, toReal_one] at h
    exact h
  -- so the two inequalities are the same matrix, at the same variables
  have e : toRealMat Z.spectraShadow.A₀
        + ∑ j : Fin Z.h, β j • toRealMat (Z.spectraShadow.A j)
      = (nominal Z).spectraShadow.A₀ + ∑ j : Fin Z.h, β j • (nominal Z).spectraShadow.A j := by
    rw [h₀]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => congrArg _ (hA j))
  exact (Iff.of_eq (congrArg Matrix.PosSemidef e)).mpr hP

theorem Zonotope.spectraShadow_contains (Z : Zonotope (Vec 𝕋 n)) :
    Z.construct ⊆ Z.spectraShadow.construct := by -- --- PROOF ---
  -- the box is carried over, so only the nominal parts are compared
  refine mono_subset (fun x hx => ?_) subset_rfl
  obtain ⟨β, hP, hx'⟩ := (Real.Zonotope.spectraShadow_exact (nominal Z)).subset hx
  change x = toRealVec Z.c
    + ∑ j : Fin Z.h, (β : Fin Z.h → ℝ) j • (fun i => toReal (Z.G j i) : Vec ℝ n) at hx'
  exact SpectraShadow.mem_nominalSet_iff.mpr
    ⟨β, Zonotope.posSemidef_spectraShadow Z β
      ((Real.Zonotope.posSemidef_spectraShadow_iff (nominal Z) β).mp hP),
      fun i => (congrFun hx' i).trans
      (Entrywise.add_sum_smul_apply (toRealVec Z.c) (fun j i => toReal (Z.G j i)) β i)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
