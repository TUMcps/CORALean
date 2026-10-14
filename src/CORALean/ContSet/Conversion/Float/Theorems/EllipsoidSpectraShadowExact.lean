module

public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidSpectraShadowExact
public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Operations.Ellipsoid_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_SpectraShadow

@[expose] public section

/-!
# An ellipsoid as a spectrahedral shadow, over a floating-point scalar

The exact layer's inequality `[[1, uᵀ], [u, I]] ⪰ 0` with `one` and `zero` as its entries, all
stored exactly, and the ellipsoid's own centre, generator matrix and error box: nothing rounds, so
nothing is paid, and the two sets are equal.

Not routed through the exact layer's set but through its *nominal* reading, the exact conversion
of the ellipsoid the stored floats describe, which shares the exactness proof.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The stored matrices read as the exact layer's inequality. -/
theorem Ellipsoid.aux_toRealMat_spectraShadow (E : Ellipsoid 𝕋 n) :
    toRealMat E.spectraShadow.A₀ = (nominal E).spectraShadow.A₀ ∧
      ∀ i, toRealMat (E.spectraShadow.A i) = (nominal E).spectraShadow.A i := by -- --- PROOF ---
  refine ⟨?_, fun i => ?_⟩
  · ext (p q : Fin (E.k + 1))
    show toReal (if p = q then (one : 𝕋) else zero) = if p = q then (1 : ℝ) else 0
    split_ifs <;> simp [toReal_zero, toReal_one]
  · ext (p q : Fin (E.k + 1))
    show toReal (if (p = 0 ∧ q = i.succ) ∨ (p = i.succ ∧ q = 0) then (one : 𝕋) else zero) =
      if (p = 0 ∧ q = i.succ) ∨ (p = i.succ ∧ q = 0) then (1 : ℝ) else 0
    split_ifs <;> simp [toReal_zero, toReal_one]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.spectraShadow_exact (E : Ellipsoid 𝕋 n) :
    E.construct = E.spectraShadow.construct := by -- --- PROOF ---
  obtain ⟨h₀, hA⟩ := Ellipsoid.aux_toRealMat_spectraShadow E
  -- the box is carried over, so only the nominal parts are compared
  show nominalSet E + (InflatedContSet.I_error E).construct = nominalSet E.spectraShadow +
    (InflatedContSet.I_error E.spectraShadow).construct
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨β, hP, hx'⟩ := (Real.Ellipsoid.spectraShadow_exact (nominal E)).subset hx
    change x = toRealVec E.c + ∑ i, β i • (fun r => toReal (E.G r i) : Vec ℝ n) at hx'
    -- the stored inequality is the exact layer's, matrix by matrix
    have e : toRealMat E.spectraShadow.A₀ + ∑ i, β i • toRealMat (E.spectraShadow.A i) =
        (nominal E).spectraShadow.A₀ + ∑ i, β i • (nominal E).spectraShadow.A i := by
      rw [h₀]
      exact congrArg _ (Finset.sum_congr rfl fun i _ => congrArg _ (hA i))
    exact SpectraShadow.mem_nominalSet_iff.mpr
      ⟨β, (Iff.of_eq (congrArg Matrix.PosSemidef e)).mpr hP, fun i => (congrFun hx' i).trans
      (Entrywise.add_sum_smul_apply (toRealVec E.c) (fun j i => toReal (E.G i j)) β i)⟩
  · intro hx
    obtain ⟨β, hP, hx'⟩ := SpectraShadow.mem_nominalSet_iff.mp hx
    have e : toRealMat E.spectraShadow.A₀ + ∑ i, β i • toRealMat (E.spectraShadow.A i) =
        (nominal E).spectraShadow.A₀ + ∑ i, β i • (nominal E).spectraShadow.A i := by
      rw [h₀]
      exact congrArg _ (Finset.sum_congr rfl fun i _ => congrArg _ (hA i))
    refine (Real.Ellipsoid.spectraShadow_exact (nominal E)).superset
      ⟨β, (Iff.of_eq (congrArg Matrix.PosSemidef e)).mp hP, ?_⟩
    funext i
    exact (hx' i).trans (Entrywise.add_sum_smul_apply (toRealVec E.c)
      (fun j i => toReal (E.G i j)) β i).symm

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
