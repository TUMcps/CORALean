module

public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.MonomialSingle
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

/-!
# A zonotope as an array of Taylor models — the construction

`Zonotope.taylm` is the construction; `Zonotope_to_Taylm` states and proves what it guarantees.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.taylm {m : ℕ} (Z : Zonotope (Vec ℝ m)) (N : ℕ) : Fin m → Taylm Z.h :=
  fun i => ⟨(Z.c i, 0) :: List.ofFn (fun j => (Z.G j i, Pi.single j 1)), 0, 0, N⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
