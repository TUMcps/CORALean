module

public import CORALean.ContSet.Interval.Float.Operations.MatVolume
public import CORALean.ContSet.Interval.Float.Theorems.VolumeNominalLe
public import CORALean.ContSet.Interval.Float.Theorems.VecNominal
public import CORALean.ContSet.Interval.Real.Theorems.MatVolumeEq

@[expose] public section

/-!
# `Interval.matVolume` bounds the Lebesgue volume

The matrices of the box, read as functions, have Lebesgue volume at most the stored bound,
`ofReal`-read. The exact layer's `matVolume` is the volume of the stacked box, whose bound is
`Interval.volume_nominal_le`.

## Inputs
* `I` – interval matrix

## Hypotheses
* none

## Conclusion
* the Lebesgue volume of the box is at most the float volume
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.matVolume_le (I : Interval (Mat 𝕋 m n)) : -- --- CONCL ---
    MeasureTheory.volume {f : Fin m → Fin n → ℝ | (Matrix.of f : Mat ℝ m n) ∈ I.construct}
      ≤ ENNReal.ofReal (toReal I.matVolume) := by -- --- PROOF ---
  have h : I.construct = I.nominal.construct := rfl
  rw [h, Real.Interval.matVolume_eq]
  have key : ∀ F : Fin m → Fin n → ENNReal, ∏ i, ∏ j, F i j =
      ∏ k : Fin (n * m), F (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1 := by
    intro F
    rw [Finset.prod_comm, ← Fintype.prod_prod_type (fun p : Fin n × Fin m => F p.2 p.1)]
    exact Fintype.prod_equiv finProdFinEquiv (fun p => F p.2 p.1) _ (fun p => by simp)
  have hv : I.nominal.matVolume = I.vec.nominal.volume :=
    key fun i j => ENNReal.ofReal (I.nominal.sup i j - I.nominal.inf i j)
  rw [hv]
  exact I.vec.volume_nominal_le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
