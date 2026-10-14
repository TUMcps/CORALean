module

public import CORALean.Global.BlockDiag
public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Theorems.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopePosSemidefSpectraShadowIff

@[expose] public section

/-!
# A polytope as a spectrahedral shadow

`HPolytope.spectraShadow_exact`: its `spectraShadow` is exactly it.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.spectraShadow_exact (P : HPolytope (Vec ℝ n)) :
    P.construct = P.spectraShadow.construct := by -- --- PROOF ---
  apply Set.eq_of_subset_of_subset
  · intro x hx
    refine ⟨x, (HPolytope.posSemidef_spectraShadow_iff P x).mpr hx, ?_⟩
    show x = 0 + ∑ i, x i • (Pi.single i 1 : Fin n → ℝ)
    rw [zero_add]
    exact HPolytope.eq_sum_single x
  · rintro _ ⟨β, hβ, rfl⟩
    show (0 + ∑ i, β i • (Pi.single i 1 : Fin n → ℝ)) ∈ P.construct
    have e : (∑ i, β i • (Pi.single i 1 : Fin n → ℝ)) = β :=
      (HPolytope.eq_sum_single β).symm
    rw [zero_add]
    exact Eq.mpr (congrArg (· ∈ P.construct) e) ((HPolytope.posSemidef_spectraShadow_iff P β).mp hβ)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
