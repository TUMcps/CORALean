module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.ContSet.Taylm.Real.Theorems.Basic
public import CORALean.ContSet.Taylm.Real.Theorems.MonomialSingle
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Zonotope.Float.Theorems.MemNominalSet
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

/-!
# A zonotope as an array of Taylor models, over a floating-point scalar — the construction

`Zonotope.taylm` is the construction; `Zonotope_to_Taylm` states and proves what it guarantees.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.taylm (Z : Zonotope (Vec 𝕋 n)) (N : ℕ) : Fin n → Taylm 𝕋 Z.h :=
  fun i => ⟨(Z.c i, 0) :: List.ofFn (fun j => (Z.G j i, Pi.single j 1)),
    Z.I_error.inf i, Z.I_error.sup i, N⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
