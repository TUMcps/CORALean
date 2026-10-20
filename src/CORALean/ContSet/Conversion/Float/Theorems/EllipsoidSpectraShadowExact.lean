module

public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidSpectraShadowExact
public import CORALean.ContSet.Ellipsoid.Float.Theorems.Basic
public import CORALean.ContSet.SpectraShadow.Float.Theorems.MemNominalSet
public import CORALean.ContSet.Conversion.Float.Operations.Ellipsoid_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_SpectraShadow

@[expose] public section

/-!
# An ellipsoid as a spectrahedral shadow, over a floating-point scalar

The exact layer's Schur form `[[1, (x - q)ᵀ], [x - q, Q]] ⪰ 0` with the stored `Q`, the negated
stored `q`, `one` and `zero` as its entries, and the ellipsoid's own error box: nothing rounds, so
nothing is paid, and the two sets are equal whenever the stored `Q` is PSD. A non-PSD stored `Q`
reads as its center alone, while its Schur form is empty, hence the hypothesis.

Not routed through the exact layer's set but through its *nominal* reading, the exact conversion
of the ellipsoid the stored floats describe, which shares the exactness proof.

## Inputs
* `E` – ellipsoid

## Hypotheses
* `hQ` – shape matrix positive semidefinite

## Conclusion
* ellipsoid equals its spectrahedral shadow
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

variable [SoundFloatArithmetic 𝕋]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- With a PSD stored `Q`, the stored inequality reads entry by entry as the exact layer's. -/
private theorem Ellipsoid.aux_toRealMat_spectraShadow (E : Ellipsoid 𝕋 n)
    (hQ : (toRealMat E.Q).PosSemidef) (β : Vec ℝ n) : -- --- CONCL ---
    toRealMat E.spectraShadow.A₀ + ∑ i, β i • toRealMat (E.spectraShadow.A i) =
      (⟨toRealMat E.Q, toRealVec E.q, hQ⟩ : Real.Ellipsoid n).spectraShadow.A₀ +
        ∑ i, β i • (⟨toRealMat E.Q, toRealVec E.q, hQ⟩ : Real.Ellipsoid n).spectraShadow.A i
    := by -- --- PROOF ---
  congr 1
  · ext (p r : Fin (n + 1))
    refine Fin.cases ?_ (fun i => ?_) p <;> refine Fin.cases ?_ (fun j => ?_) r <;>
      simp [toRealMat, toRealVec, Ellipsoid.spectraShadow, Real.Ellipsoid.spectraShadow,
        toReal_one, toReal_neg']
  · refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
    ext (p r : Fin (n + 1))
    show toReal (if (p = 0 ∧ r = i.succ) ∨ (p = i.succ ∧ r = 0) then (one : 𝕋) else zero) =
      if (p = 0 ∧ r = i.succ) ∨ (p = i.succ ∧ r = 0) then (1 : ℝ) else 0
    split_ifs <;> simp [toReal_zero, toReal_one]

/-- The shadow's point is its free variable. -/
private theorem Ellipsoid.aux_point_spectraShadow (E : Ellipsoid 𝕋 n) (β : Vec ℝ n) (i : Fin n) :
    toReal (E.spectraShadow.c i) + ∑ j, toReal (E.spectraShadow.G j i) * β j = β i := by
  simp [Ellipsoid.spectraShadow, apply_ite toReal, toReal_zero, toReal_one]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.spectraShadow_exact (E : Ellipsoid 𝕋 n)
    (hQ : (toRealMat E.Q).PosSemidef) : -- --- CONCL ---
    E.construct = E.spectraShadow.construct := by -- --- PROOF ---
  -- the box is carried over, so only the nominal parts are compared
  show nominalSet E + (InflatedContSet.I_error E).construct = nominalSet E.spectraShadow +
    (InflatedContSet.I_error E.spectraShadow).construct
  congr 1
  ext x
  rw [SpectraShadow.mem_nominalSet_iff]
  change x ∈ (nominal E).ellipsoid.construct ↔ _
  rw [Ellipsoid.nominal_of_psd hQ]
  constructor
  · intro hx
    refine ⟨x, ?_, fun i => (Ellipsoid.aux_point_spectraShadow E x i).symm⟩
    exact (Iff.of_eq (congrArg Matrix.PosSemidef
      (Ellipsoid.aux_toRealMat_spectraShadow E hQ x))).mpr
      ((Real.Ellipsoid.posSemidef_spectraShadow_iff _ x).mpr hx)
  · rintro ⟨β, hβ, hx⟩
    obtain rfl : x = β := funext fun i => (hx i).trans (Ellipsoid.aux_point_spectraShadow E β i)
    exact (Real.Ellipsoid.posSemidef_spectraShadow_iff _ x).mp ((Iff.of_eq (congrArg
      Matrix.PosSemidef (Ellipsoid.aux_toRealMat_spectraShadow E hQ x))).mp hβ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
