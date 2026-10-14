module

public import CORALean.ContSet.Conversion.Real.Interval_to_Zonotope
public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.MonomialSingle
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil

@[expose] public section

/-!
# A box as an array of Taylor models — the construction

`Interval.taylm` is the construction; `Interval_to_Taylm` states and proves what it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.taylm (I : Interval (Vec ℝ n)) (N : ℕ) : Fin n → Taylm n :=
  fun i => ⟨[((I.inf i + I.sup i) / 2, 0), ((I.sup i - I.inf i) / 2, Pi.single i 1)], 0, 0, N⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
