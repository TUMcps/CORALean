module

public import CORALean.ContSet.SpectraShadow.Real.Theorems.IsBoundedIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.RepresentsaEmptySetIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.SupportFuncEqBotIff
public import CORALean.ContSet.SpectraShadow.Real.Theorems.Basic
public import CORALean.ContSet.Interval.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval

@[expose] public section

/-!
# A spectrahedral shadow's interval hull
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
noncomputable def SpectraShadow.interval (S : SpectraShadow (Vec ℝ n)) : Interval (Vec ℝ n) :=
  if S.representsa_emptySet then Interval.empty n
  else ⟨fun i => -(S.supportFunc (-(LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ))).toReal,
        fun i => (S.supportFunc (LinearMap.proj i : Vec ℝ n →ₗ[ℝ] ℝ)).toReal⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
