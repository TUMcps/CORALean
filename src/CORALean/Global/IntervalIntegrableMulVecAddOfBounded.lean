module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# A linear field along a continuous state under a bounded input is integrable

`A x + u`, measurable on `T`, with `x` continuous on `T` and `u` in a bounded set there, is
bounded on every compact window `[0, t] ⊆ T` — `‖A‖` times the state's bound plus the input's —
and so integrable over it. It is what a linear run's integral equation needs of its integrand,
given only that the input set is bounded, which every representation of a set of points is.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The field `A x + u`, measurable on the window from `0` to `t` and bounded there by the
state's continuity and `U`'s boundedness, is integrable over it. -/
theorem intervalIntegrable_mulVec_add_of_bounded {A : Mat ℝ n n} {T : Set ℝ} {U : Set (Vec ℝ n)}
    {x u : ℝ → Vec ℝ n} (hx : ContinuousOn x T)
    (hm : AEStronglyMeasurable (fun s => A *ᵥ x s + u s) (volume.restrict T))
    (hu : ∀ t ∈ T, u t ∈ U) (hU : Bornology.IsBounded U) {t : ℝ}
    (hUIcc : Set.uIcc 0 t ⊆ T) : -- --- STMT ---
    IntervalIntegrable (fun s => A *ᵥ x s + u s) volume 0 t := by -- --- PROOF ---
  have hUo : Set.uIoc (0:ℝ) t ⊆ Set.uIcc 0 t := Set.uIoc_subset_uIcc
  obtain ⟨Cx, hCx⟩ := (isCompact_uIcc (a := (0:ℝ)) (b := t)).exists_bound_of_continuousOn
    (hx.mono hUIcc)
  obtain ⟨Cu, hCu⟩ := hU.exists_norm_le
  have hfin : volume (Set.uIoc (0:ℝ) t) < ⊤ := by
    rcases le_total 0 t with h | h
    · rw [Set.uIoc_of_le h]; exact measure_Ioc_lt_top
    · rw [Set.uIoc_of_ge h]; exact measure_Ioc_lt_top
  -- `‖A‖ Cx + Cu` bounds the integrand on the window, giving a finite integral
  rw [intervalIntegrable_iff]
  refine ⟨hm.mono_measure (Measure.restrict_mono (hUo.trans hUIcc) le_rfl),
    HasFiniteIntegral.restrict_of_bounded (C := ‖A‖ * Cx + Cu) hfin ?_⟩
  refine (ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
  calc ‖A *ᵥ x s + u s‖
      ≤ ‖A *ᵥ x s‖ + ‖u s‖ := norm_add_le _ _
    _ ≤ ‖A‖ * Cx + Cu :=
        add_le_add (le_trans (Matrix.linfty_opNorm_mulVec _ _)
          (mul_le_mul_of_nonneg_left (hCx _ (hUo hs)) (norm_nonneg _)))
          (hCu _ (hu s (hUIcc (hUo hs))))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
