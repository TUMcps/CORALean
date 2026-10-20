module

public import CORALean.ContSet.SpectraShadow.Real.Operations.SingletonOne

@[expose] public section

/-!
# `singletonOne` is the point `1`

The inequality `diag(1 - β, β - 1) ⪰ 0` has the diagonal entries `1 - β` and `β - 1`, so it holds
only at `β = 1`, and then it is the zero matrix: the set is the point `{1}`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* `singletonOne` is the point `1`
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.singletonOne_construct :
    SpectraShadow.singletonOne.construct = {fun _ => 1} := by -- --- PROOF ---
  ext x
  constructor
  -- both diagonal entries of the matrix are non-negative: `1 - β ≥ 0` and `β - 1 ≥ 0`
  · rintro ⟨β, hβ, rfl⟩
    have h1 := hβ.diag_nonneg (i := (0 : Fin 2))
    have h2 := hβ.diag_nonneg (i := (1 : Fin 2))
    simp [SpectraShadow.singletonOne] at h1 h2 ⊢
    have : β 0 = 1 := by linarith
    funext i
    simp [this]
  -- at `β = 1` the matrix is zero
  · rintro rfl
    refine ⟨fun _ => 1, ?_, by simp [SpectraShadow.singletonOne]⟩
    have : SpectraShadow.singletonOne.A₀ + ∑ i, (fun _ : Fin 1 => (1 : ℝ)) i •
        SpectraShadow.singletonOne.A i = (0 : Mat ℝ 2 2) := by
      ext p q
      fin_cases p <;> fin_cases q <;> simp [SpectraShadow.singletonOne]
    show Matrix.PosSemidef (SpectraShadow.singletonOne.A₀ + ∑ i, (fun _ : Fin 1 => (1 : ℝ)) i •
        SpectraShadow.singletonOne.A i)
    rw [this]
    exact Matrix.PosSemidef.zero

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
